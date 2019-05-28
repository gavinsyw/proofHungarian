Require Import Edges.


Section GRAPH.

Print U_set.

Print Vertex.

Print V_set.

Inductive Graph : V_set -> A_set -> Type :=
  | G_empty : Graph V_empty A_empty
  | G_vertex :
      forall (v : V_set) (a : A_set) (d : Graph v a) (x : Vertex),
      ~ v x -> Graph (V_union (V_single x) v) a
  | G_edge :
      forall (v : V_set) (a : A_set) (d : Graph v a) (x y : Vertex),
      v x ->
      v y ->
      x <> y ->
      ~ a (A_ends x y) -> ~ a (A_ends y x) -> Graph v (A_union (E_set x y) a)
  | G_eq :
      forall (v v' : V_set) (a a' : A_set),
      v = v' -> a = a' -> Graph v a -> Graph v' a'.

Inductive BiGraph : V_set -> V_set -> A_set -> Type:=
  | B_empty : BiGraph V_empty V_empty A_empty
  | B_vertexA :
      forall (v1 v2 : V_set) (a : A_set) (d : BiGraph v1 v2 a) (x : Vertex), ~ v1 x -> ~v2 x -> BiGraph (V_union (V_single x) v1) v2 a
  | B_vertexB :
      forall (v1 v2 : V_set) (a : A_set) (d : BiGraph v1 v2 a) (x : Vertex), ~ v1 x -> ~v2 x -> BiGraph v1 (V_union (V_single x) v2) a
  | B_edge :
      forall (v1 v2 : V_set) (a : A_set) (d : BiGraph v1 v2 a) (x y : Vertex), v1 x -> v2 y -> ~a (A_ends x y) -> ~a (A_ends y x) -> BiGraph v1 v2 (A_union (E_set x y) a)
  | B_eq :
      forall (v1 v2 v1' v2' : V_set) (a a' : A_set),
      v1 = v1' -> v2 = v2' -> a = a' -> BiGraph v1 v2 a -> BiGraph v1' v2' a'.

Definition Matching (v1 v2: V_set) (a: A_set) (b: BiGraph v1 v2 a) :  Prop :=
  match b with
  |
  
  
  
Definition Matchinglist := list Matching. 


Inductive Matching : V_set -> V_set -> A_set  -> Type:=
  | M_empty : Matching V_empty V_empty A_empty (B).