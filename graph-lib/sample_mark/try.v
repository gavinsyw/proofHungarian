Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import floyd.proofauto.
Require Import floyd_ext.exists_trick.


Goal forall x y: Z, exists (x' y': Z) (H: x = y + (x' - y')), x - y = x' - y' /\ H = H.
intros.
do 3 eexists.
remember (x - y) eqn: HH.
rewrite HH.
gather_current_goal_with_evar.
Grab Existential Variables.


Focus 2.
split; reflexivity.
omega.







Variables A B C: Type.

Variable F: B -> C.

Definition equiv (x y: B) : Prop := F x = F y.
Instance eqB: Equivalence equiv. Admitted.

Variable f: B -> A.

Instance fp: Proper (equiv ==> (@eq A)) f. Admitted.

Goal forall x y: B, F x = F y -> f x = f y.
intros.
assert (equiv x y) by auto.

SearchAbout Equivalence.

Locate RewriteRelation.
rewrite H.

(*
(* Example 1, Fail*)
Goal exists x: nat, forall y: nat, x <= y.
eexists.
intros.
instantiate (1 := y).

(* Example 2, Succeed*)
Goal exists x: nat, forall y: nat, x <= y.
eexists.
intros.
instantiate (1 := 0).
*)

Lemma exists_aux: forall P: Prop, (exists H: P, H = H) -> P.
Proof.
  intros.
  destruct H; auto.
Qed.

Goal exists x: nat, exists H: (forall y: nat, x <= y), H = H /\ (exists x: nat, exists H: (forall y: nat, x <= y), H = H).
Proof.
  eexists.
  eexists.
  split; [reflexivity |].
  apply exists_aux.
  eexists. auto.
  Grab Existential Variables.
Focus 2.
  + intros. induction y; simpl; auto.
  eexists.
  eexists.
reflexivity.
  Grab Existential Variables.
   intros. induction y; simpl; auto.
Qed.

Add LoadPath "/Users/Qinxiang/Downloads/exploit-plugin-master/src" as Exploit.
Declare ML Module "src/exploit_tactic".

Goal forall A B C D G, (A -> B -> C -> D) -> G.
intros.
exploit X.

SearchAbout ex_intro.

(* Example 3, Fail*)
Goal exists x: nat, exists H: (forall y: nat, x <= y), H = H.
Proof.
  eexists.
  eexists.
  instantiate (3 := 0).
  assert (forall y, 0 <= y) as H.
    intros. induction y; simpl; auto.
  instantiate (1 := H).
  auto.
Qed.





Lemma foo: forall y, 0 <= y.
intros. induction y; simpl; auto.
Qed.

Goal exists x: nat, exists H: (forall y: nat, x <= y), H = H.
Proof.
  eexists.
  eexists.
  instantiate (3 := 0).
  instantiate (1 := foo).
  auto.
Qed.

generalize (@eq_refl Prop). intro HH.
instantiate (1 := HH).
apply H.
  assert (forall H: Prop, H = H) as HH by (intros; reflexivity).
(*  instantiate (1 := HH). *)

(* Example 4, Succeed*)
Goal exists x: (forall H: Prop, H = H), x = x.
Proof.
  eexists.
  pose proof ((fun H: Prop => eq_refl) : forall H: Prop, H = H) as HH.
  instantiate (1 := HH).
  instantiate (1 := fun H: Prop => eq_refl).