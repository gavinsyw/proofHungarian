Require Import RamifyCoq.CertiGC.bitwise_encoding.
Require Import VST.floyd.proofauto.

Class tagint_lossless {A : Type} (tcA : tagcode A) : Type :=
  til_bound: (tc_bitsize tcA <= Int.wordsize)%nat.

Definition int_of_tag {A : Type} `{tcA : tagcode A} : A -> int :=
  fun a => Int.repr (tc_encode tcA a).

Definition tag_of_int {A : Type} `{tcA : tagcode A} : int -> A :=
  fun i => tc_decode tcA (Int.unsigned i).

Lemma tag_of_int_of_tag {A} `{tcA : tagcode A} `{tcAl: @tagint_lossless A tcA}: forall a,
  tag_of_int (int_of_tag a) = a.
Proof.
  intros.
  red in tcAl. unfold tag_of_int, int_of_tag.
  rewrite Int.unsigned_repr. apply tc_decode_encode.
  generalize (tc_encode_range tcA a); intro.
  unfold Int.max_unsigned. unfold Int.modulus.
  apply two_power_nat_le in tcAl.
  omega.
Qed.

Lemma int_of_tag_modu {A} {B} `{tcA : tagcode A} `{tcB : tagcode B}:
  forall a b, Int.modu (@int_of_tag (A * B) (prod_tc tcA tcB) (a,b)) 
                      (Int.repr (two_power_nat (tc_bitsize tcB))) =
              int_of_tag b.
Proof.
  intros.
  unfold int_of_tag. simpl.
(* SearchAbout Int.modu. *)
Admitted.

Lemma int_of_tag_divu {A} {B} `{tcA : tagcode A} `{tcB : tagcode B}:
  forall a b, Int.divu (@int_of_tag (A * B) (prod_tc tcA tcB) (a,b)) 
                      (Int.repr (two_power_nat (tc_bitsize tcB))) =
              int_of_tag a.
Proof.
  intros.
  unfold int_of_tag. simpl.
(* SearchAbout Int.divu. *)
Admitted.
