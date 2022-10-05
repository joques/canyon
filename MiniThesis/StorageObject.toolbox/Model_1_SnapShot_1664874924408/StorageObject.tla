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

EXTENDS Integers, FiniteSets                      \*introduce Integers modules and Naturals

CONSTANTS Nodes, Edges, Root, MaxCardinality    \* we use MaxCardinality instead of Infinity

(*
for parent nodes including the root we will denote as key
for edges we will denote as ver (version)

node n has a neighbor m such that ver(n) to ver(m) + 1 or ver(m) + x where x is an positive integer 
*)

VARIABLE object, controlState, subControlState, key, Ver

TypeOK == /\ controlState \in {"Start", "mmiddle", "done"}
          /\ subControlState \in {"Lf", "Pt", "Co"}
          /\ key  \in [Nodes -> Nodes]
          /\ Ver \in [Nodes -> Nat]
          
ASSUME /\ Root \in Nodes
       /\ \A e \in Edges : (e \subseteq Nodes) /\ (Cardinality(e) = 2)
       /\ MaxCardinality \in Nat
       /\ MaxCardinality >= Cardinality(Nodes)

(* We will denote versions as a set of neighbors of node n in the graph joined by an edge to n
*)

Versions(n) == {m \in Nodes : {m, n} \in Edges}


(*
wE NOW SPECIFY THE ALGORITHM 
*) 

vars == <<key, Ver>>

         

Init == /\ key = [n \in Nodes |-> n]
        /\ Ver = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]
        
Next == \E n \in Nodes :
          \E m \in Versions(n) : 
             /\ Ver[m] < 1 + Ver[n]
             /\ \E d \in (Ver[m]+1) .. (Ver[n] - 1) :
                    /\ Ver' = [Ver EXCEPT ![n] = d]
                    /\ key'  = [key  EXCEPT ![n] = m]

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)




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
\* Last modified Tue Oct 04 11:13:43 CAST 2022 by goodwill
\* Created Tue Oct 04 09:12:06 CAST 2022 by goodwill
