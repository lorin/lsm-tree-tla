(*

# Operations

* get
* upsert
* delete

## get
Return NIL if the key is not in the store

## insert
Always returns "ok"


## delete

Always returns "ok"

*)
---- MODULE kvstore ----
CONSTANTS Keys, Vals, MISSING, NIL

Ops == {"get", "upsert", "delete"}

ASSUME MISSING \notin Vals
ASSUME NIL \notin Vals \union Ops \union {MISSING}

VARIABLES op,
    args,
    ret,
    state,
    dict \* tracks mapping of keys to values

TypeOK ==
    /\ args \in {<<k>>: k \in Keys} \union {<<k,v>>: k \in Keys, v \in Vals} \union {NIL}
    /\ dict \in [Keys -> Vals \union {MISSING}]
    /\ op \in Ops \union {NIL} \* initial state for Ops is NIL
    /\ ret \in Vals \union {"ok", MISSING, NIL}
    /\ state \in {"ready", "working"}

Init ==
    /\ op = NIL
    /\ args = NIL
    /\ ret = NIL
    /\ dict = [k \in Keys |-> MISSING]
    /\ state = "ready"

GetReq(key) ==
    /\ state = "ready"
    /\ op' = "get"
    /\ args' = <<key>>
    /\ ret' = NIL
    /\ state' = "working"
    /\ UNCHANGED dict

GetResp == LET key == args[1] IN
    /\ op = "get"
    /\ ret' = dict[key]
    /\ state' = "ready"
    /\ UNCHANGED <<op, args, dict>>

UpsertReq(key, val) ==
    /\ state = "ready"
    /\ op' = "upsert"
    /\ args' = <<key, val>>
    /\ ret' = NIL
    /\ state' = "working"
    /\ UNCHANGED <<dict>>

Present(key) == dict[key] \in Vals
Absent(key) == dict[key] = MISSING

UpsertResp == LET key == args[1]
                  val == args[2] IN
       /\ op = "upsert"
       /\ state = "working"
       /\ dict' = [dict EXCEPT ![key] = val]
       /\ ret' = "ok"
       /\ state' = "ready"
       /\ UNCHANGED <<op, args>>

DeleteReq(key) ==
    /\ state = "ready"
    /\ op' = "delete"
    /\ args' = <<key>>
    /\ ret' = NIL
    /\ state' = "working"
    /\ UNCHANGED dict

\* we permit deleting keys that aren't there
DeleteResp ==
    LET key == args[1]
    IN /\ op = "delete"
       /\ ret' = "ok"
       /\ state' = "ready"
       /\ dict' = [dict EXCEPT ![key]=MISSING]
       /\ UNCHANGED <<op, args>>

Next == \/ \E k \in Keys: 
           \/ GetReq(k)
           \/ DeleteReq(k)
           \/ \E v \in Vals: UpsertReq(k, v)  
        \/ GetResp
        \/ UpsertResp
        \/ DeleteResp

vars == <<op, args, ret, dict, state>>

Spec == Init /\ [][Next]_vars

====