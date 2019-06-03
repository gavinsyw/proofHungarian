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

Inductive step (bg: BiGraph): Vertex -> Vertex -> Prop :=
  | step_intro: forall e x y, evalid bg e -> src bg e = x -> dst bg e = y -> step bg x y.

Definition edge (bg: BiGraph) (n n' : Vertex) : Prop :=
  v1 bg n /\ v2 bg n' /\ step bg n n'.

Print path.

Notation Gph := (PreGraph Vertex Edge).

Definition strong_evalid (bg: BiGraph) (e: Edge) : Prop :=
  evalid bg e /\ ((v1 bg (src bg e) /\ v2 bg (dst bg e)) \/ (v1 bg (dst bg e) /\ v2 bg (src bg e))).

Fixpoint valid_path' (g: BiGraph) (p: list Edge) : Prop :=
  match p with
    | nil => True
    | n :: nil => strong_evalid g n
    | n1 :: ((n2 :: _) as p') => strong_evalid g n1 /\ dst g n1 = src g n2 /\ valid_path' g p'
  end.

Definition valid_path (g: BiGraph) (p: path) :=
  match p with
  | (v, nil) => (v1 g v \/ v2 g v)
  | (v, (e :: _) as p') => v = src g e /\ valid_path' g p'
  end.

Definition commonVertex (bg: BiGraph) (e1 e2: Edge) : Prop := strong_evalid bg e1 /\ strong_evalid bg e2 /\ ~(src bg e1 = src bg e2) /\ ~(src bg e1 = dst bg e2) /\ ~(dst bg e1 = src bg e2) /\ ~(dst bg e1 = dst bg e2).

Fixpoint noCross (bg: BiGraph) (e: Edge) (p: list Edge) : Prop :=
  match p with
    | nil => True
    | n1 :: (_ as p') => ~commonVertex bg e n1 /\ noCross bg e p'
  end.

Fixpoint matching (bg: BiGraph) (p: list Edge) : Prop :=
  match p with
    | nil => True
    | n1 :: (_ as p') => noCross bg n1 p'
  end.

Definition maxMatching (bg: BiGraph) (p: list Edge) : Prop := matching bg p /\ ~(exists p': list Edge, matching bg p' /\ length p' > length p).

Definition matchingPoint (bg: BiGraph) (p: list Edge) (v: Vertex) : Prop := matching bg p /\ exists e: Edge, In e p /\ (src bg e = v \/ dst bg e = v).

Definition augEdge (bg: BiGraph) (p: list Edge) (e: Edge) : Prop := matching bg p /\ ((matchingPoint bg p (src bg e) /\ ~matchingPoint bg p (dst bg e)) \/ (~matchingPoint bg p (src bg e) /\ matchingPoint bg p (dst bg e))).

Fixpoint augPath' (bg: BiGraph) (p le: list Edge) : Prop :=
  match p with
    | nil => True
    | e :: (_ as p') => matching bg le /\ augPath' bg p' le /\ augEdge bg le e
  end.

Fixpoint augPath (bg: BiGraph) (p: path) (le: list Edge) : Prop :=
  match p with
    | (v, nil) => True
    | (v, (e :: _ as p')) => v = src bg e /\ matching bg le /\ valid_path bg p /\ augPath' bg p' le /\ augEdge bg le e
  end.

Definition noAugPath (bg: BiGraph) (le: list Edge) : Prop := forall p: path, augPath bg p le -> snd p = nil.

Theorem Hungurian: forall (bg: BiGraph) (le: list Edge), matching bg le -> noAugPath bg le -> maxMatching bg le.
Proof.
  intros.
  unfold maxMatching.
  split.
  exact H.
  unfold not; intros.
  repeat destruct H1.
Admitted.

End biGraph.