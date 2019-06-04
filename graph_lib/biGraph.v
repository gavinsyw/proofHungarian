Require Import RamifyCoq.graph.find_not_in.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_ind.
Require Import Coq.Logic.ProofIrrelevance.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.lib.Equivalence_ext.
Section biGraph.

(*备注：文件中有一部分定义同时用Inductive和Fixpoint等价地定义，因为不知道哪种更方便，故现都保留*)

Context {Vertex Edge: Type}.

Record BiGraph {EV: EqDec Vertex eq} {EE: EqDec Edge eq} := {
  v1 : Ensemble Vertex;
  v2 : Ensemble Vertex;
  evalid : Ensemble Edge;
  src : Edge -> Vertex;
  dst : Edge -> Vertex;
}.

Context {EV: EqDec Vertex eq}.
Context {EE: EqDec Edge eq}.

(*一步可达*)
Inductive step (bg: BiGraph): Vertex -> Vertex -> Prop :=
  | step_intro: forall e x y, evalid bg e -> src bg e = x -> dst bg e = y -> step bg x y.

(* 由点定义的二分图的边*)
Definition edge (bg: BiGraph) (n n' : Vertex) : Prop :=
  ((v1 bg n /\ v2 bg n') \/ (v2 bg n /\ v1 bg n')) /\ step bg n n'.

Print path.

(*由边定义的二分图的边*)
Definition strong_evalid (bg: BiGraph) (e: Edge) : Prop :=
  evalid bg e /\ ((v1 bg (src bg e) /\ v2 bg (dst bg e)) \/ (v1 bg (dst bg e) /\ v2 bg (src bg e))).

Fixpoint valid_path' (g: BiGraph) (p: list Edge) : Prop :=
  match p with
    | nil => True
    | n :: nil => strong_evalid g n
    | n1 :: ((n2 :: _) as p') => strong_evalid g n1 /\ dst g n1 = src g n2 /\ valid_path' g p'
  end.

(*二分图中的合法路径*)
Definition valid_path (g: BiGraph) (p: path) :=
  match p with
  | (v, nil) => (v1 g v \/ v2 g v)
  | (v, (e :: _) as p') => v = src g e /\ valid_path' g p'
  end.

(* 
Definition noCommonVertex (bg: BiGraph) (e1 e2: Edge) : Prop := strong_evalid bg e1 /\ strong_evalid bg e2 /\ ~(src bg e1 = src bg e2) /\ ~(src bg e1 = dst bg e2) /\ ~(dst bg e1 = src bg e2) /\ ~(dst bg e1 = dst bg e2).

Fixpoint noCross (bg: BiGraph) (e: Edge) (p: Ensemble Edge) : Prop :=
  match p with
    | Empty_set Edge => strong_evalid bg e
    | n1 :: (_ as p') => noCommonVertex bg e n1 /\ noCross bg e p'
  end. *)

(*匹配*)
Inductive matching (bg: BiGraph) :
  Ensemble Vertex ->  list Edge -> Prop :=
  | emptyMatch : matching bg (Empty_set Vertex) nil
  | normalMatch: forall (v: Ensemble Vertex) (p: list Edge) (e: Edge), strong_evalid bg e -> ~Ensembles.In _ v (src bg e) -> ~Ensembles.In _ v (dst bg e) -> matching bg (Ensembles.Add Vertex (Ensembles.Add Vertex v (src bg e)) (dst bg e)) (e::p).

(* 
Fixpoint matching (bg: BiGraph) (p: list Edge) : Prop :=
  match p with
    | nil => True
    | n1 :: (_ as p') => noCross bg n1 p'
  end. *)

(*最大匹配*)
Definition maxMatching (bg: BiGraph) (v: Ensemble Vertex)(p: list Edge) : Prop := matching bg v p -> forall (v': Ensemble Vertex) (p': list Edge), matching bg v' p' -> length p' <= length p.
Search Ensemble.

(*匹配点*)
Definition matchingPoint (bg: BiGraph) (ve: Ensemble Vertex)(p: list Edge) (v: Vertex) : Prop := matching bg ve p -> Ensembles.In _ ve v.

(* Definition augEdge (bg: BiGraph) (p: list Edge) (e: Edge) : Prop := matching bg p /\ ((matchingPoint bg p (src bg e) /\ ~matchingPoint bg p (dst bg e)) \/ (~matchingPoint bg p (src bg e) /\ matchingPoint bg p (dst bg e))).
 *)

(*增广路径（无起始点），一次添加两条路*)
Fixpoint augPath' (bg: BiGraph) (ve: Ensemble Vertex) (p le: list Edge) : Prop :=
  match p with
    | nil => True
    | e :: nil => ~matchingPoint bg ve le (src bg e) /\ ~matchingPoint bg ve le (src bg e)
    | e1 :: e2 ::_ as p' => (In e2 le /\ ~In e1 le)
  end.

(*正式的增广路径定义，需要起点是非匹配点*)
Definition augPath (bg: BiGraph) (p: path) (ve: Ensemble Vertex) (le: list Edge) : Prop :=
  match p with
    | (v, _ as p') => (v1 bg v \/ v2 bg v) ->~Ensembles.In _ ve v -> augPath' bg ve p' le
  end.

(*无增广路径*)
Definition noAugPath (bg: BiGraph) (ve: Ensemble Vertex) (le: list Edge) : Prop := forall p: path, augPath bg p ve le -> snd p = nil.

(*匈牙利算法的正确性充分条件：如果没有增广路径，那么当前匹配是最大匹配*)
Theorem Hungurian: forall (bg: BiGraph) (ve: Ensemble Vertex) (le: list Edge), matching bg ve le -> noAugPath bg ve le -> maxMatching bg ve le.
Proof.
  intros.
  unfold maxMatching; intros.
Admitted.

(*匈牙利算法的正确性必要条件：如果当前匹配是最大匹配，那么不存在增广路径（Theorem）；等价地（Lemma），如果有增广路径，那么一定存在一条更大的匹配*)
Lemma rev_Hungarian': forall (bg: BiGraph) (ve: Ensemble Vertex) (le: list Edge), ~noAugPath bg ve le -> ~maxMatching bg ve le.
Proof.
  intros.
  unfold maxMatching; unfold not; intros.
Admitted.

Theorem rev_Hungarian: forall (bg: BiGraph) (ve: Ensemble Vertex) (le: list Edge), maxMatching bg ve le -> noAugPath bg ve le.
Proof.
  pose proof rev_Hungarian'.
Admitted.

End biGraph.