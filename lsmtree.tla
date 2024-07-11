---- MODULE lsmtree ----
EXTENDS TLC, Naturals

CONSTANTS NTrees, NKeys, Vals,
          NIL, TOMBSTONE, MISSING,
          READY,
          GET_VALUE

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
        CASE key \in keysOf[focus] /\ val # TOMBSTONE    -> val
          [] key \in keysOf[focus] /\ val = TOMBSTONE    -> MISSING
          [] key \notin keysOfFocus /\ next[focus] # NIL -> GET_VALUE
          [] OTHER                                       -> MISSING
       /\ UNCHANGED <<memtable, next, keysOf, valOf, free, compaction, op, args>>





TypeOk == 
    /\ memtable \in Trees
    /\ next \in [Trees -> Trees \union {NIL}]
    /\ keysOf \in [Trees -> SUBSET Keys]
    /\ valOf \in [Trees \X Keys -> Vals \union {MISSING, TOMBSTONE}]
    /\ free \in SUBSET Trees

Next == 
    \/ \E k \in Keys : GetReq(k)
    \/ GetReponse
====