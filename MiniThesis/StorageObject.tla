--------------------------- MODULE StorageObject ---------------------------
(*
Fot the Object Specification We will use the Spaning Tree Algorithm and modify it to suit our needs 
The Spanning tree Allows for the Groth and also control and identifying neighbors 

This can be changed to parent-chlid and will allow operations shuch as 
1. update (promotion to parent) and create child
2. Delete (remove child and downgrade from parent to child and change to done)
3. write ( will only be done on initial root as all children must come from root node)
4. read (locate the child ( Reference parents and Grand parents { incremental update read }

The naming conventions are subject to change if need be 

The object will have two control states
controState and subControlState

controState: This will be a set of initial States ( Start, middle and done)
    Start: indicates that no current version exists and must be created
    middle: indicates that child nodes (versions ) exists and can be updated
    done: indicated that:
        1. No more child nodes can be created
        2. Terminationi has occured 
        3. Hopefully return last version as Child of 

subControlState:
    Lf: indicates a leaf node (last child) {last version on that branch}
    Pt: indicates a node became a parent
    Co: indicates  back tracking neighbor nodes to the root. ( list of app parents conected to current node)


*)

EXTENDS Integers, FiniteSets, Randomization                      \*introduce Integers modules and Naturals*\

CONSTANTS Nodes, Root, MaxCardinality    \* we use MaxCardinality instead of Infinity*\

(*
for parent nodes including the root we will denote as key
for edges we will denote as ver (version)

node n has a neighbor m such that ver(n) to ver(m) + 1 or ver(m) + x where x is an positive integer 
*)

VARIABLE object, controlState, subControlState, key, Ver, Edges

TypeOK == /\ controlState \in {"Start", "middle", "done"}
          /\ subControlState \in {"Lf", "Pt", "Co"}
          /\ key  \in [Nodes -> Nodes]
          /\ Ver \in [Nodes -> Nat]
          
ASSUME /\ Root \in Nodes
       /\ MaxCardinality \in Nat
       /\ MaxCardinality >= Cardinality(Nodes)

(* We will denote versions as a set of neighbors of node n in the graph joined by an edge to n
*)

Versions(n) == {m \in Nodes : {m, n} \in Edges}


(*
wE NOW SPECIFY THE ALGORITHM 
*) 

vars == <<key, Ver, Edges>> \* or child nodes instead Childnodes (how many child nodes is linked to  current parent *\

         
\* initial write function*\

Init == /\ key = [n \in Nodes |-> n]
        /\ Ver = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]
        /\ Edges \in {E \in SUBSET (SUBSET Nodes) : \A e \in E : Cardinality(e) = 2}
        /\ controlState = "middle"
        /\ subControlState = "Pt" 

(* All Methods to incorporate

vars == <<timestamp, values, deliverQueues>>
nodeIds == 1..N_NODES

\Prepares to read   *\
DeliverSet(n, T, t, k, v) ==
  values' = [
      values EXCEPT ![n] = {<<tp, kp, vp>> \in values[n] : tp \notin T} \union { <<t, k, v>> }
    ]

\* Clears current read req *\
DeliverDelete(n, T) ==
  values' = [
    values EXCEPT ![n] = {<<t, k, v>> \in values[n] : t \notin T}
  ]

\* Checks read Commad and Parents connected to it *\
Deliver(n, command, payload) ==
  \/ command = "set"
    /\ DeliverSet(n, payload[1], payload[2], payload[3], payload[4])
  \/ command = "delete"
    /\ DeliverDelete(n, payload)

\* Prints Tree Graph with Children *\
Broadcast(n, command, payload) ==
  /\ Deliver(n, command, payload)
  /\ deliverQueues' = [
      i \in nodeIds |->
        IF i = n THEN
          deliverQueues[i]
        ELSE
          Append(deliverQueues[i], <<command, payload>>)
      ]

\* UpdateWrite Checks if not deleted and if can be updated *\
RequestSet(n, k, v) ==  
  LET matches == {<<t, kp, vp>> \in values[n] : k = kp}  IN
  LET T == {t : <<t, kp, vp>> \in matches}  IN
    /\ timestamp' = timestamp + 1
    /\ Broadcast(n, "set", <<T, timestamp, k, v>>)

\* Checks if we can Delete *\
RequestDelete(n, k) ==
  LET matches == {<<t, kp, v>> \in values[n] : k = kp}  IN
  LET T == {t : <<t, kp, v>> \in matches}  IN
    /\ T /= {}
    /\ Broadcast(n, "delete", T)


\* UpdateWrite Action *\
RequestSetOnNode ==
  /\ timestamp < MAX_TIMESTAMP
  /\ \E <<n, k, v>> \in nodeIds \X KEYS \X VALUES : RequestSet(n, k, v)

\* Checks vurrent Version and if node exists *\
RequestDeleteOnNode ==
  /\ \E <<n, k>> \in nodeIds \X KEYS : RequestDelete(n, k)
  /\ UNCHANGED timestamp


\* ReadNote *\
DeliverOnNode ==
  \E n \in nodeIds :
    /\ Len(deliverQueues[n]) > 0
    /\ \E <<command, payload>> \in {Head(deliverQueues[n])} :
        Deliver(n, command, payload)
    /\ deliverQueues' = [deliverQueues EXCEPT ![n] = Tail(deliverQueues[n])]
  /\ UNCHANGED timestamp

\* Checks if there are not Children nodes *\
DeliverQueuesIsEmpty ==
  \A n \in nodeIds: Len(deliverQueues[n]) = 0


\* Deleting Action  *\
Terminating ==
  /\ DeliverQueuesIsEmpty
  /\ UNCHANGED vars 


*)

        
(* I need to define my next state based on the functions I will define
    Write
    Update
    Delete
    Read
    
    as follows
    
    Next == \/ writeRoot
            \/ UpdateWrte
            \/ ReadNode
            \/ DeleteNdoe
            
    /* my spec will then be *\
    
    Spec == Init /\ [][Next]_var /\Wf_vars(ReadNode)



*)        
Next == \E n \in Nodes :
          \E m \in Versions(n) : 
             /\ Ver[m] < 1 + Ver[n]
             /\ \E d \in (Ver[m]+1) .. (Ver[n] - 1) :
                    /\ Ver' = [Ver EXCEPT ![n] = d]
                    /\ key'  = [key  EXCEPT ![n] = m]


\* Inital call*\
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
(*
\* update Function*\

UpdateWrite(key, ver) == Init /\ [][Next]_vars /\ WF_vars(Next)

\*Delete Function *\


\*Update unction *\

*)

\*Checking if the parent nodes are correct *\
PostCondition == 
  \A n \in Nodes :
    \/ /\ n = Root 
       /\ Ver[n] = 0
       /\ key[n] = n
    \/ /\ Ver[n] = MaxCardinality 
       /\ key[n] = n
       /\ \A m \in Versions(n) : Ver[m] = MaxCardinality
    \/ /\ Ver[n] \in 1..(MaxCardinality-1)
       /\ key[n] \in Versions(n)
       /\ Ver[n] = Ver[key[n]] + 1






Safety == []((~ ENABLED Next) => PostCondition)




Liveness == <>(~ ENABLED Next) 
























 
=============================================================================
\* Modification History
\* Last modified Tue Oct 04 13:03:23 CAST 2022 by goodwill
\* Created Tue Oct 04 09:12:06 CAST 2022 by goodwill
