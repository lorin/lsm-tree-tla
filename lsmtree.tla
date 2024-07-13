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

Keys == 1..NKeys


MISSING == CHOOSE MISSING : MISSING \notin Vals

Ops == {"get", "upsert", "delete"}

Rets == {"ok", MISSING} \union Vals

Args == [1..1 -> Keys] \union Keys \X Vals

NIL == CHOOSE NIL : NIL \notin UNION {Keys, Vals, Ops, Args, Rets, {MISSING}}


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

MemtableAtCapacity == Cardinality(keysOf[memtable]) = THRESHOLD

UpsertReq(key, val) ==
    /\ state = READY
    \* To avoid deadlock, we need to either be below capacity or there has to be at least one free node so we can flush to disk if needed
    /\ MemtableAtCapacity => free # {}
    /\ state' = UPSERT_RESPONSE
    /\ op' = "upsert"
    /\ args' = <<key, val>>
    /\ ret' = NIL
    /\ UNCHANGED <<memtable, next, keysOf, valOf, free, compaction, focus>>


DeleteReq(key) ==
    /\ state = READY
    \* To avoid deadlock, we need to either be below capacity or there has to be at least one free node so we can flush to disk if needed
    /\ MemtableAtCapacity => free # {}
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


\* Write memtable to disk
WriteToDisk ==
    LET disktree == (CHOOSE tree \in free : TRUE) IN 
       /\ state = WRITE_TO_DISK
       /\ free # {}
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
reachable(n) == IF n = NIL
                THEN {} 
                ELSE {n} \union reachable(next[n])

\* Trees that are stored on disk
onDisk == reachable(next[memtable])

\* Trees that are currently in the process of being compacted
compacting == UNION {x.old : x \in compaction}

prev(n) == IF       \E p \in Trees : next[p] = n
           THEN CHOOSE p \in Trees : next[p] = n
           ELSE NIL


\* Set of sequences of length 2 or greater that represent on-disk trees.
\* These form our candidates for compaction
runs == {S \in SUBSET onDisk : \E h, t \in S : 
                /\ {next[h], prev(t)} \subseteq S 
                /\ \A n \in S \ {h,t} : {next[n], prev(n)} \subseteq S}

\* The set of runs that are not currently involved in compaction
candidates == {S \in runs : S \intersect compacting = {}}

\** Start compacting a collection of trees
StartCompaction == 
    \* there must be a candidate set where none of the candidates are involved in compacting
    LET new == CHOOSE n \in free: TRUE
    IN 
    /\ candidates # {}
    /\ free # {}
    /\ compaction' \in {compaction \union {[old|->x, new|->new]} : x \in candidates}
    /\ free' = free \ {new}
    /\ UNCHANGED<<memtable, next, keysOf, valOf, op, args, ret, state, focus>>


TypeOk == 
    /\ op \in Ops \union {NIL}
    /\ args \in Args \union {NIL}
    /\ ret \in Rets \union {NIL}
    /\ memtable \in Trees
    /\ next \in [Trees -> Trees \union {NIL}]
    /\ keysOf \in [Trees -> SUBSET Keys]
    /\ valOf \in [Trees \X Keys -> Vals \union {MISSING, TOMBSTONE}]
    /\ free \in SUBSET Trees
    /\ compaction \subseteq [old: SUBSET Trees, new: Trees]

Next == 
    \/ \E k \in Keys : GetReq(k)
    \/ \E k \in Keys, v \in Vals : UpsertReq(k, v)
    \/ GetResponse
    \/ UpsertResponse
    \/ DeleteResponse
    \/ WriteToDisk
    \/ StartCompaction

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