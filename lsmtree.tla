---- MODULE lsmtree ----
EXTENDS TLC, Naturals, FiniteSets

CONSTANTS NTrees, NKeys, Vals,
          TOMBSTONE, 
          THRESHOLD,

         \* program states
          READY,
          GET_VALUE,
          UPSERT_RESPONSE,
          WRITE_TO_DISK


NIL == CHOOSE NIL : NIL \notin Vals
MISSING == CHOOSE MISSING : MISSING \notin (Vals \union {NIL})

VARIABLES memtable,
          next,
          keysOf,
          valOf,
          free,
          op,
          args,
          ret,
          compaction,
          state,
          focus

Keys == 1..NKeys
Trees == 1..NTrees

Init == 
    /\ memtable = CHOOSE t \in Trees: TRUE
    /\ next = [t \in Trees |-> NIL]
    /\ keysOf = [t \in Trees |-> {}]
    /\ valOf = [t \in Trees, k \in Keys |-> MISSING]
    /\ free = Trees \ {memtable}
    /\ op = NIL
    /\ args = NIL
    /\ ret = NIL
    /\ compaction = {}
    /\ state = READY
    /\ focus = NIL

GetReq(key) ==
    /\ state = READY
    /\ op' = "get"
    /\ args' = <<key>>
    /\ ret' = NIL
    /\ state' = GET_VALUE
    /\ focus' = memtable
    /\ UNCHANGED <<memtable, next, keysOf, valOf, free, compaction>>

GetResponse == 
    LET key == args[1]
        val == valOf[focus, key]
    IN /\ state = GET_VALUE
       /\ state' = IF key \in keysOf[focus] \/ next[focus] = NIL
                   THEN READY
                   ELSE GET_VALUE
       /\ focus' = next[focus]
       /\ ret' = 
        CASE key \in keysOf[focus] /\ val # TOMBSTONE      -> val
          [] key \in keysOf[focus] /\ val = TOMBSTONE      -> MISSING
          [] key \notin keysOf[focus] /\ next[focus] # NIL -> GET_VALUE
          [] OTHER                                         -> MISSING
       /\ UNCHANGED <<memtable, next, keysOf, valOf, free, compaction, op, args>>

UpsertReq(key, val) ==
    /\ state = READY
    /\ state' = UPSERT_RESPONSE
    /\ op' = "upsert"
    /\ args' = <<key, val>>
    /\ ret' = NIL
    /\ UNCHANGED <<memtable, next, keysOf, valOf, free, compaction, focus>>

MemtableAtCapacity == Cardinality(keysOf[memtable]) = THRESHOLD


UpsertResponse ==
    LET key == args[1]
        val == args[2] IN
    /\ state = UPSERT_RESPONSE
    /\ ret' = "ok"
    /\ state' = IF MemtableAtCapacity THEN WRITE_TO_DISK ELSE READY
    /\ keysOf' = [keysOf EXCEPT ![memtable]=@ \union {key}]
    /\ valOf' = [valOf EXCEPT ![memtable, key]=val]
    /\ UNCHANGED <<op, args, free, compaction, focus, next>>


\* Write memtable to disk
WriteToDisk ==
    LET disktree == (CHOOSE tree \in free : TRUE) IN 
       /\ state = WRITE_TO_DISK
       /\ next' = [next EXCEPT ![memtable]=disktree]
       /\ keysOf' = [keysOf EXCEPT ![memtable]={}, ![disktree]=keysOf[memtable]]
       /\ valOf' = [t \in Trees, k \in Keys |-> 
                        CASE t = disktree -> valOf[memtable, k]
                          [] t = memtable  -> MISSING
                          [] OTHER        -> valOf[t, k] ]
       /\ free' = free \ {disktree}
       /\ state' = READY
       /\ UNCHANGED <<op, args, ret, compaction, focus>>



TypeOk == 
    /\ memtable \in Trees
    /\ next \in [Trees -> Trees \union {NIL}]
    /\ keysOf \in [Trees -> SUBSET Keys]
    /\ valOf \in [Trees \X Keys -> Vals \union {MISSING, TOMBSTONE}]
    /\ free \in SUBSET Trees

Next == 
    \/ \E k \in Keys : GetReq(k)
    \/ \E k \in Keys, v \in Vals : UpsertReq(k, v)
    \/ GetResponse
    \/ UpsertResponse
    \/ WriteToDisk

====