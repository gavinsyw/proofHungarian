Require Import Coq.Logic.ProofIrrelevance.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.lib.Equivalence_ext.


Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.

Require Import  Coq.omega.Omega.
Require Import Coq.Logic.Classical.

Require Import RamifyCoq.graph_definition.

Arguments clos_refl_trans {A} _ _ _.
Arguments clos_refl_trans_1n {A} _ _ _.
Arguments clos_refl_trans_n1 {A} _ _ _.

Section Aug.

Lemma match_smaller: forall v a m, Ma v (a :: m) = None -> Ma v m = None /\ v <> fst a.
Proof.
  intros.
  unfold Ma in H.
  Search Nat.eqb.
  pose proof classic (src BG a = v).
  destruct H0.
  + rewrite H0 in H.
    rewrite Nat.eqb_refl in H.
    repeat split; inversion H.
  + Search (_ =? _).
    pose proof Nat.eqb_neq (src BG a) v.
    destruct H1.
    specialize (H2 H0).
    rewrite H2 in H.
    repeat split.
    - auto.
    - unfold src in H0.
      auto.
Qed.

Lemma notmatching_to_aug_exist_1:
  forall v v', Matching v = None -> In v' (con v) -> Matching v' = None -> aug_path ((v, v')::nil).
Proof.
  intros.
  unfold aug_path.
  unfold Matching in H.
  unfold Matching in H1.
  induction M.
  + unfold In. auto.
  + apply match_smaller in H.
    apply match_smaller in H1.
    destruct H.
    destruct H1.
    specialize (IHm H H1).
    Search In.
    pose proof in_inv.
    remember (v, v') as a'.
    specialize (H4 _ a a' m).
    assert (a <> a' /\ ~In a' m -> ~ In a' (a :: m)).
    { tauto. }
    subst a'.
    induction a.
    assert ((a, b) <> (v, v')).
    {
      unfold not.
      intros.
      injection H6.
      intros.
      unfold fst in H2.
      rewrite H8 in H2.
      destruct H2.
      reflexivity.
    }
    tauto.
Qed.


Lemma match_smaller:
  forall e m, is_matching (e::m) -> is_matching m.
Proof.
  intros.
  inversion H.
  unfold disjoint_edges_set in H0.
  unfold is_matching.
  unfold disjoint_edges_set.
  split; intros.
  + specialize (H0 e1 e2).
    (* in_cons: forall (A : Type) (a b : A) (l : list A), In b l -> In b (a :: l) *)
    pose proof in_cons.
    pose proof (H6 _ e _ _ H2).
    pose proof (H6 _ e _ _ H3).
    tauto.
  + specialize (H1 e0).
    pose proof in_cons.
    pose proof (H3 _ e _ _ H2).
    specialize (H1 H4).
    (* in_eq: forall (A : Type) (a : A) (l : list A), In a (a :: l) *)
    pose proof in_eq e m.
    Admitted.

Lemma greater_match_to_exception:
  forall m, is_matching m -> length m > length M -> (exists e, In e m /\ ~ In e M).
Proof.
  intros.
  revert M base_Match_re H0.
  induction m; intros.
  + inversion H0.
  + inversion H0.
    - Admitted.

Lemma greater_match_to_cross_path:
  forall m e, is_matching m -> length m > length M -> In e m /\ ~ In e M -> (exists p, cross_path p /\ In e p).
Proof.
  intros.
  induction m.
  + inversion H0.
  + Admitted.

Theorem greater_match_to_aug_path:
  forall m, is_matching m -> length m > length M -> (exists e p, In e m /\ ~ In e M /\ aug_path p /\ In e p).
Proof.
  intros.
  pose proof greater_match_to_exception _ H H0.
  destruct H1.
  pose proof greater_match_to_cross_path _ _ H H0 H1.
  Admitted.




