------------------------------- MODULE Index -------------------------------
CONSTANTS   Key,            \* The set of all keys.
            Val,            \* The set of all values.
            ObjId           \* The set of all objects IDs.
VARIABLES   store,          \* A data store mapping keys to values.
            object,         \* The set of open Opath objects.
            path,  \* Opaths of the store for each objects.
            written,        \* A log of writes performed within each objects.
            missed          \* The set of writes invisible to each objects.
----------------------------------------------------------------------------
NoVal ==    \* Choose something to represent the absence of a value.
    CHOOSE v : v \notin Val

Store ==    \* The set of all key-value stores.
    [Key -> Val \cup {NoVal}]

Init == \* The initial predicate.
    /\ store = [k \in Key |-> NoVal]        \* All store values are initially NoVal.
    /\ object = {}                              \* The set of open objects is initially empty.
    /\ path =                      \* All path values are initially NoVal.
        [t \in ObjId |-> [k \in Key |-> NoVal]]
    /\ written = [t \in ObjId |-> {}]        \* All write logs are initially empty.
    /\ missed = [t \in ObjId |-> {}]         \* All missed writes are initially empty.
    
TypeInvariant ==    \* The type invariant.
    /\ store \in Store
    /\ object \subseteq ObjId
    /\ path \in [ObjId -> Store]
    /\ written \in [ObjId -> SUBSET Key]
    /\ missed \in [ObjId -> SUBSET Key]
    
objectLifecycle ==
    /\ \A t \in object :    \* If store != Opath & we haven't written it, we must have missed a write.
        \A k \in Key : (store[k] /= path[t][k] /\ k \notin written[t]) => k \in missed[t]
    /\ \A t \in ObjId \ object : \* Checks objects are cleaned up after disposal.
        /\ \A k \in Key : path[t][k] = NoVal
        /\ written[t] = {}
        /\ missed[t] = {}

Openobject(t) ==    \* Open a new objects.
    /\ t \notin object
    /\ object' = object \cup {t}
    /\ path' = [path EXCEPT ![t] = store]
    /\ UNCHANGED <<written, missed, store>>

Write(t, k, v) == \* Using objects t, write value v to the store under key k.
    /\ t \in object
    /\ path[t][k] = NoVal
    /\ path' = [path EXCEPT ![t][k] = v]
    /\ written' = [written EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED <<object, missed, store>>
    
Update(t, k, v) ==  \* Using objects t, update the value associated with key k to v.
    /\ t \in object
    /\ path[t][k] \notin {NoVal, v}
    /\ path' = [path EXCEPT ![t][k] = v]
    /\ written' = [written EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED <<object, missed, store>>
    

Rollbackobject(t) ==    \* Close the objects without merging writes into store.
    /\ t \in object
    /\ object' = object \ {t}
    /\ path' = [path EXCEPT ![t] = [k \in Key |-> NoVal]]
    /\ written' = [written EXCEPT ![t] = {}]
    /\ missed' = [missed EXCEPT ![t] = {}]
    /\ UNCHANGED store

Closeobject(t) ==   \* Close objects t, merging writes into store.
    /\ t \in object
    /\ missed[t] \cap written[t] = {}   \* Detection of write-write conflicts.
    /\ store' =                         \* Merge path writes into store.
        [k \in Key |-> IF k \in written[t] THEN path[t][k] ELSE store[k]]
    /\ object' = object \ {t}
    /\ missed' =    \* Update the missed writes for other open objects.
        [otherobject \in ObjId |-> IF otherobject \in object' THEN missed[otherobject] \cup written[t] ELSE {}]
    /\ path' = [path EXCEPT ![t] = [k \in Key |-> NoVal]]
    /\ written' = [written EXCEPT ![t] = {}]

Next == \* The next-state relation.
    \/ \E t \in ObjId : Openobject(t)
    \/ \E t \in object : \E k \in Key : \E v \in Val : Write(t, k, v)
    \/ \E t \in object : \E k \in Key : \E v \in Val : Update(t, k, v)
    \/ \E t \in object : Rollbackobject(t)
    \/ \E t \in object : Closeobject(t)
        
Spec == \* Initialize state with Init and transition with Next.
    Init /\ [][Next]_<<store, object, path, written, missed>>
----------------------------------------------------------------------------
THEOREM Spec => [](TypeInvariant /\ objectLifecycle)
=============================================================================
\* Modification History
\* Last modified Fri Oct 28 12:27:00 CAST 2022 by goodwill
\* Created Tue Oct 25 02:49:34 CAST 2022 by goodwill
