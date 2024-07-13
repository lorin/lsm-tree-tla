---- MODULE lsmtree ----
EXTENDS TLC, Naturals, FiniteSets

CONSTANTS NTrees, NKeys, Vals,
          TOMBSTONE, 
          THRESHOLD,

         \* program states
          READY,
          GET_VALUE,
          UPSERT_RESPONSE,
          DELETE_RESPONSE,
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
          [] key \notin keysOf[focus] /\ next[focus] # NIL -> ret
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

DeleteReq(key) ==
    /\ state = READY
    /\ op' = "delete"
    /\ args' = <<key>>
    /\ ret' = NIL
    /\ state' = DELETE_RESPONSE
    /\ focus' = memtable
    /\ UNCHANGED <<memtable, next, keysOf, valOf, free, compaction>>

DeleteResponse ==
    LET key == args[1] IN 
    /\ state = DELETE_RESPONSE
    /\ ret' = "ok"
    /\ state' = IF MemtableAtCapacity THEN WRITE_TO_DISK ELSE READY
    /\ keysOf' = [keysOf EXCEPT ![memtable]=@ \union {key}]
    /\ valOf' = [valOf EXCEPT ![memtable, key]=TOMBSTONE]
    /\ UNCHANGED <<op, args, free, memtable, compaction, focus, next>>

UpsertResponse ==
    LET key == args[1]
        val == args[2] IN
    /\ state = UPSERT_RESPONSE
    /\ state' = IF MemtableAtCapacity THEN WRITE_TO_DISK ELSE READY
    /\ ret' = "ok"
    /\ keysOf' = [keysOf EXCEPT ![memtable]=@ \union {key}]
    /\ valOf' = [valOf EXCEPT ![memtable, key]=val]
    /\ UNCHANGED <<op, args, free, memtable, compaction, focus, next>>

SpaceLeft == free # {}

\* Write memtable to disk
WriteToDisk ==
    LET disktree == (CHOOSE tree \in free : TRUE) IN 
       /\ state = WRITE_TO_DISK
       /\ SpaceLeft
       /\ next' = [next EXCEPT ![memtable]=disktree, ![disktree]=next[memtable]]
       /\ keysOf' = [keysOf EXCEPT ![memtable]={}, ![disktree]=keysOf[memtable]]
       /\ valOf' = [t \in Trees, k \in Keys |-> 
                        CASE t = disktree -> valOf[memtable, k]
                          [] t = memtable  -> MISSING
                          [] OTHER        -> valOf[t, k] ]
       /\ free' = free \ {disktree}
       /\ state' = READY
       /\ ret' = "ok"
       /\ UNCHANGED <<memtable, op, args, compaction, focus>>



\* The set of nodes reachable from a given node based on the `next` relationship.
\* This is also known as reflexive transitive closure
RECURSIVE reachable(_)
reachable(n) == IF n = NIL THEN {} ELSE {n} \UNION reachable(next[n])

\* Trees that are stored on disk
onDisk == reachable(next[memtable])

\* Trees that are currently in the process of being compacted
compacting == UNION {x.old : x \in compaction}

prev(n) == IF       \E p \in Trees : next[p] = n
           THEN CHOOSE p \in Trees : next[p] = n
           ELSE NIL

candidates == {S \in SUBSET onDisk : \E h, t \in S : 
                /\ {next[h], prev(t)} \subseteq S 
                /\ \A n \in S \ {h,t} : {next[n], prev(n)} \subseteq S
}

\** Start compacting a collection of trees
\* StartCompaction == 


TypeOk == 
    /\ memtable \in Trees
    /\ next \in [Trees -> Trees \union {NIL}]
    /\ keysOf \in [Trees -> SUBSET Keys]
    /\ valOf \in [Trees \X Keys -> Vals \union {MISSING, TOMBSTONE}]
    /\ free \in SUBSET Trees
    /\ compaction \in [old: SUBSET Trees, new: Trees]

Next == 
    \/ \E k \in Keys : GetReq(k)
    \/ \E k \in Keys, v \in Vals : UpsertReq(k, v)
    \/ GetResponse
    \/ UpsertResponse
    \/ DeleteResponse
    \/ WriteToDisk

\*
\* Refinement mapping
\*
RECURSIVE Get(_, _)

Get(node, key) == 
    LET keys == keysOf[node]
        present == key \in keys
        val == valOf[node, key]
    IN CASE node = NIL              -> MISSING
      [] present /\ val # TOMBSTONE -> val
      [] present /\ val = TOMBSTONE -> MISSING
      [] OTHER                      -> Get(next[node], key)

kvDict == [key \in Keys |-> Get(memtable, key)]
kvState == IF state \in {READY, WRITE_TO_DISK} THEN "ready" ELSE "working"
Alias == [
    op |-> op,
    args |-> args,
    ret |-> ret, 
    kvState |-> kvState, 
    kvDict |-> kvDict,
    memtable |-> memtable,
    disktree |-> next[memtable],
    keysOf |-> keysOf,
    valOf |-> valOf,
    next |-> next
    ]

Mapping == INSTANCE kvstore
    WITH dict <- kvDict,
         state <- kvState

Refinement == Mapping!Spec
====