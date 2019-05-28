Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.StrongInduction.
Require Import Coq.micromega.Tauto.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.NArith.BinNat.

Definition boolV := nat.
Definition lit : Type := boolV*bool.
Definition clauses : Type := lit*lit.
Definition twoCNF : Type := list clauses.
Definition injec : Type := boolV -> bool.

Section Evaluation.
Variable i : injec.

Definition liteval (l :lit) : bool :=
  match snd l with
  | true => i (fst l)
  | false => negb (i (fst l))
  end.

Definition cleval (c : clauses) : bool := orb (liteval (fst c)) (liteval (snd c)).

Fixpoint cnfeval (cn : twoCNF) : bool :=
  match cn with
  | nil => true
  | c' :: cn' => match cleval c' with
                 | false => false
                 | true => cnfeval cn'
                 end
  end.

Definition cltrue (c : clauses) : Prop := 
  liteval (fst c) = true /\ liteval (snd c) = true.

Definition cnftrue (cn : twoCNF) : Prop :=
  forall c, In c cn -> cleval c = true.

End Evaluation.

Definition t1 : boolV := 1.
Definition tb1 : lit := (t1, false).
Definition tb2 : lit := (t1, true).
Definition c1 : clauses := (tb1, tb2).
Definition c2 : clauses := (tb2, tb1).
Definition tcnf : twoCNF := c2 :: nil.

Section TwoSat.

Variable tc : twoCNF.

Definition checkV (l : lit) : Prop :=
  exists cl, In cl tc /\ (fst (fst cl) = fst l \/ fst (snd cl) = fst l).

Definition checkE (te : nat*bool) : Prop :=
  fst te < length tc.

Definition Reversebool (tb : lit) : lit :=
  match snd tb with
  | true => (fst tb, false)
  | false => (fst tb, true)
  end.

Definition nthcl (n : nat) : clauses :=
  nth n tc c1.

Definition st (clb : nat*bool) : lit :=
  match snd clb with
  | true => Reversebool (fst (nthcl (fst clb)))
  | false => Reversebool (snd (nthcl (fst clb)))
  end.

Definition ed (clb : nat*bool) : lit :=
  match snd clb with
  | true => snd (nthcl (fst clb))
  | false => fst (nthcl (fst clb))
  end.

Definition necessary (l1 l2 : lit) : Prop :=
  forall i, cnftrue i tc -> checkV l1 -> checkV l2 -> 
  liteval i l1 = true -> liteval i l2 = true.

Lemma neg_Reverselit : forall l i, 
  negb (liteval i l) = liteval i (Reversebool l).
Proof.
  intros. unfold Reversebool.
  case l. simpl. intros.
  case b0.
  + unfold liteval. simpl. reflexivity.
  + unfold liteval. simpl. apply negb_involutive.
Qed.

Lemma Reverse_checkV : forall l, checkV l <-> checkV (Reversebool l).
Proof.
  intros l. case l. intros. unfold checkV. unfold Reversebool. simpl.
  split. 
  + intros. case b0.
    - simpl. unfold checkV in H. simpl in H. apply H.
    - simpl. unfold checkV in H. simpl in H. apply H.
  + case b0.
    - intros. simpl. unfold checkV in H. simpl in H. apply H.
    - intros. simpl. unfold checkV in H. simpl in H. apply H.
Qed.

Lemma Re_necessary :
  forall l1 l2, necessary l1 l2 -> necessary (Reversebool l2) (Reversebool l1).
Proof.
  unfold necessary. intros.
  apply Reverse_checkV in H1. apply Reverse_checkV in H2.
  pose proof H i H0 H2 H1.
  destruct (liteval i l1) eqn:HH.
  + assert (HH0 : true = true). reflexivity. pose proof H4 HH0.
    rewrite <- neg_Reverselit in H3. apply negb_true_iff in H3.
    rewrite H3 in H5. congruence.
  + rewrite <- neg_Reverselit. rewrite HH. unfold negb.
    reflexivity.
Qed.

Print PreGraph.
Check Build_PreGraph.

Definition GraphGen : PreGraph lit (nat*bool) :=
  {| vvalid := checkV;
     evalid := checkE;
     src := st;
     dst := ed;
  |}.

End TwoSat.

Section Proof0.

Lemma not_checkVnill : forall l, checkV nil l -> False.
Proof.
  intros.
  unfold checkV in H. destruct H.
  destruct H. simpl in H. apply H.
Qed.

Lemma Re_Re : forall l, Reversebool (Reversebool l) = l.
Proof.
  intros. case l. intros. case b0.
  + unfold Reversebool. simpl. reflexivity.
  + unfold Reversebool. simpl. reflexivity.
Qed.

Lemma reach_eq_nece: forall l1 l2 tc, checkV tc l1 -> checkV tc l2 -> 
  (reachable (GraphGen tc) l1 l2 <-> necessary tc l1 l2).
Proof.
  Admitted. (*
  intros. rewrite reachable_ind2_reachable in H. 
  induction H.
  + unfold necessary. intros. apply H2.
  + destruct H0. destruct H1. destruct H2.
    unfold necessary. intros.
    simpl in H3, H4.
    rewrite <- H4 in H8. rewrite <- H5.
    generalize H8, H3.
    unfold st, ed. case e. simpl. intros n b.
    unfold cleval in H.
    specialize (H (nthcl tc n)). intros. unfold checkE in H10.
    simpl in H10. unfold nthcl in H. 
    eapply nth_In in H10. pose proof H H10.
    apply orb_true_iff in H11. generalize H9. case b.
      { destruct H11.
      * intros. rewrite <- neg_Reverselit in H12. rewrite <- H5 in H9.
        apply no_fixpoint_negb in H9. eapply False_ind. apply H9.
      * intros. apply H5.
      }
      { destruct H9.
      * intros. apply H9.
      * intros. rewrite <- neg_Reverselit in H10. 
        apply negb_true_iff in H10. unfold nthcl in H10.
        rewrite H10 in H9. apply diff_false_true in H9.
        eapply False_ind. apply H9.
      }
Qed.*)

End Proof0.

Definition GraphSat (tc : twoCNF) : Prop :=
  forall l, checkV tc l ->
  ~(reachable (GraphGen tc) l (Reversebool l) 
  /\ reachable (GraphGen tc) (Reversebool l) l).
  
Lemma ReverseEdge: forall l1 l2 tc, 
  checkV tc l1 -> checkV tc l2 -> reachable (GraphGen tc) l1 l2 ->
  reachable (GraphGen tc) (Reversebool l2) (Reversebool l1).
Proof.
  intros. pose proof reach_eq_nece _ _ _ H H0.
  apply H2 in H1. pose proof Re_necessary _ _ _ H1.
  pose proof Reverse_checkV tc l1. apply H4 in H.
  pose proof Reverse_checkV tc l2. apply H5 in H0.
  pose proof reach_eq_nece _ _ _ H0 H.
  apply H6 in H3. apply H3.
Qed.

Section taggedgraph.
Variable tc : twoCNF.
Definition tag : Type := lit -> option bool.

Record legal_tag (t : tag) : Prop := {
  Pr0 : forall l b, checkV tc l -> t l = Some b ->
  t (Reversebool l) = Some (negb b);
  Pr1 : forall l1 l2, checkV tc l1 -> checkV tc l2 ->
  ~(t l1 = Some true /\ t l2 = Some false /\ 
  reachable (GraphGen tc) l1 l2);
  Pr2 : forall l1 l2, checkV tc l1 -> checkV tc l2 ->
  ~(t l1 = Some true /\ t l2 = None /\ 
  reachable (GraphGen tc) l1 l2)
  }.

Definition NullTag : tag :=
  fun x => None.

Definition FullTag (t : tag) : Prop :=
  forall l, checkV tc l -> t l <> None.
  
Record RProp (t1 t2 : tag) (x : lit) : Prop := {
  RPr0 : forall x' b', t1 x' = Some b' -> t2 x' = Some b';
  RPr1 : forall x', t1 x' = None -> reachable (GraphGen tc) x x' <->
        t2 x' = Some true;
  RPr2 : forall x', t1 x' = None -> reachable (GraphGen tc) x' (Reversebool x) <->
              t2 x' = Some false;
  RPr3 : forall x', t1 x' = None -> ~(reachable (GraphGen tc) x x' \/ reachable (GraphGen tc) x' (Reversebool x)) <->
              t2 x' = None
  }.
  
Inductive Rtaggedgraph : tag -> tag -> Prop :=
  |fully_tagged : forall t, FullTag t -> Rtaggedgraph t t
  |next_tag : forall t1 t2 t3 x , checkV tc x /\ t1 x = None -> 
              ~ reachable (GraphGen tc) x (Reversebool x) ->
              RProp t1 t2 x ->
              Rtaggedgraph t2 t3 -> Rtaggedgraph t1 t3.
              
Definition UnTagged (t : tag) (ll : list lit) : Prop :=
  forall l, In l ll <-> (checkV tc l /\ t l = None).

Lemma NullisLegal : legal_tag NullTag.
Proof.
  split.
  + intros. unfold NullTag. unfold NullTag in H0. congruence.
  + intros. unfold NullTag. apply or_not_and. left. unfold not.
    intros. inversion H1.
  + intros. unfold NullTag. apply or_not_and. left. unfold not.
    intros. inversion H1.
Qed.

Lemma ReverseNoneTag : forall l t, legal_tag t -> checkV tc l ->  
  t l = None -> t (Reversebool l) = None.
Proof.
  intros. pose proof Reverse_checkV tc l.
  destruct H2. pose proof H2 H0.
  clear H2. clear H3. 
  destruct H. destruct (t (Reversebool l)) eqn:HH.
  + generalize HH. case b.
    - intros. pose proof Pr3 _ _ H4 HH0. rewrite Re_Re in H.
      rewrite H1 in H. congruence.
    - intros. pose proof Pr3 _ _ H4 HH0. rewrite Re_Re in H.
      rewrite H1 in H. congruence.
  + reflexivity.
Qed.

Lemma NoNone2False : forall t l1 l2, legal_tag t -> 
  checkV tc l1 -> checkV tc l2 ->
  ~(t l1 = None /\ t l2 = Some false /\ 
  reachable (GraphGen tc) l1 l2).
Proof.
  intros. pose proof ReverseNoneTag _ _ H H0.
  destruct H. unfold not. intros. destruct H. destruct H3.
  pose proof H2 H. pose proof Pr3 _ _ H1  H3. unfold negb in H6.
  pose proof ReverseEdge _ _ _ H0 H1 H4.
  pose proof Reverse_checkV tc l1. apply H8 in H0.
  pose proof Reverse_checkV tc l2. apply H9 in H1.
  pose proof Pr5 _ _ H1 H0.
  unfold not in H10. destruct H10. split.
  + apply H6.
  + split. apply H5. apply H7.
Qed.

Lemma OneofThree (t : tag) : forall l1 l2, GraphSat tc -> legal_tag t ->
  checkV tc l1 -> checkV tc l2 -> 
  ~ reachable (GraphGen tc) l1 (Reversebool l1) ->
  ~(reachable (GraphGen tc) l1 l2 /\ reachable (GraphGen tc) l2 (Reversebool l1)).
Proof.
  intros. unfold GraphSat in H.
  unfold not. intros.
  destruct H4. pose proof reachable_trans _ _ _ _ H4 H5.
  apply H3. apply H6.
Qed.

Lemma OneinThree : forall (t : tag) (l : lit), 
  t l <> Some true -> t l <> None -> t l = Some false.
Proof.
  intros.
  destruct (t l) as [[|]|]; try congruence.
Qed. 

Lemma RPropisLegal : forall t1 t2 x, GraphSat tc ->
  legal_tag t1 -> checkV tc x -> t1 x = None -> 
  ~ reachable (GraphGen tc) x (Reversebool x) ->
  RProp t1 t2 x -> legal_tag t2.
Proof.
  intros.
  rename H0 into lt. split.
  - intros. unfold GraphSat in H. rename H4 into rp.
    pose proof H l H0. destruct (t2 l) eqn:HH0.
    * pose proof Pr0 _ lt _ _ H0 HH0. 
      pose proof RPr0 _ _ _ rp _ _ H6.
      generalize H6, H7, H5, HH0. case b.
      ++ case b0. { intros. apply H9. } 
                  { intros. pose proof RPr0 _ _ _ rp _ _ HH1.     rewrite H10 in H11. congruence. }
      ++ case b0. { intros. pose proof RPr0 _ _ _ rp _ _ HH1. rewrite H10 in H11. congruence. }
                  { intros. apply H9. }
    * generalize H5. destruct b eqn:HH1.
      ++ intros. pose proof RPr1 _ _ _ rp _ HH0. 
         apply H7 in H6.
         pose proof ReverseEdge _ _ _ H1 H0 H6.
         pose proof ReverseNoneTag _ _ lt H1 H2.
         pose proof ReverseNoneTag _ _ lt H0 HH0.
         pose proof RPr2 _ _ _ rp _ H10.
         apply H11 in H8. unfold negb. apply H8.
      ++ intros. pose proof RPr2 _ _ _ rp _ HH0.
         apply H7 in H6.
         pose proof ReverseNoneTag _ _ lt H1 H2.
         pose proof Reverse_checkV tc x. apply H9 in H1.
         pose proof ReverseEdge _ _ _ H0 H1 H6.
         pose proof ReverseNoneTag _ _ lt H0 HH0.
         rewrite Re_Re in H10.
         pose proof RPr1 _ _ _ rp _ H11.
         apply H12 in H10. unfold negb. apply H10.
  - intros. unfold GraphSat in H. rename H4 into rp.
    unfold not. intros. destruct H4. destruct H6.
    destruct (t2 l1) eqn:HH1.
    * destruct (t2 l2) eqn:HH2.
      ++ destruct b. { destruct b0. 
         { pose proof RPr0 _ _ _ rp _ _ HH2.
           rewrite H6 in H8. congruence. } 
         { pose proof Pr1 _ lt _ _ H0 H5. unfold not in H8. 
           destruct H8. split. apply HH1. 
           split. apply HH2. apply H7. } }
         { pose proof RPr0 _ _ _ rp _ _ HH1. 
           rewrite H4 in H8. congruence. }
      ++ destruct b. 
         { pose proof RPr2 _ _ _ rp _ HH2. apply H8 in H6.
           pose proof reachable_trans _ _ _ _ H7 H6.
           pose proof ReverseNoneTag _ _ lt H1 H2.
           pose proof Reverse_checkV tc x. apply H11 in H1.
           pose proof Pr2 _ lt _ _ H0 H1. 
           unfold not in H12. destruct H12.
           split. apply HH1. split. apply H10. apply H9. }
         { pose proof RPr0 _ _ _ rp _ _ HH1. 
           rewrite H4 in H8. congruence. }
    * destruct (t2 l2) eqn:HH2.
      ++ destruct b. { pose proof RPr0 _ _ _ rp _ _ HH2. 
         rewrite H6 in H8. congruence. }
         { pose proof RPr1 _ _ _ rp _ HH1. apply H8 in H4.
           pose proof reachable_trans _ _ _ _ H4 H7. 
           pose proof NoNone2False _ _ _ lt H1 H5. 
           unfold not in H10. destruct H10. split. 
           apply H2. split. apply HH2. apply H9. }
      ++ pose proof RPr2 _ _ _ rp _ HH2. apply H8 in H6.
         pose proof reachable_trans _ _ _ _ H7 H6.
         pose proof RPr2 _ _ _ rp _ HH1. apply H10 in H9.
         rewrite H4 in H9. congruence.
  - intros. rename H4 into rp. unfold GraphSat in H.
    unfold not. intros. destruct H4. destruct H6.
    destruct (t2 l1) eqn:HH1.
    * destruct (t2 l2) eqn:HH2.
      ++ pose proof RPr0 _ _ _ rp _ _ HH2. 
         rewrite H8 in H6. congruence.
      ++ destruct b. 
         { pose proof Pr2 _ lt _ _ H0 H5. unfold not in H8.
           destruct H8. split. apply HH1. split. 
           apply HH2. apply H7. }
         { pose proof RPr0 _ _ _ rp _ _ HH1. 
           rewrite H8 in H4. congruence. }
    * destruct (t2 l2) eqn:HH2.
      ++ pose proof RPr0 _ _ _ rp _ _ HH2. 
         rewrite H8 in H6. congruence.
      ++ pose proof RPr1 _ _ _ rp _ HH1. apply H8 in H4.
         pose proof reachable_trans _ _ _ _ H4 H7.
         pose proof RPr1 _ _ _ rp _ HH2. apply H10 in H9.
         rewrite H6 in H9. congruence.
Qed.

Lemma RisLegal : forall t1 t2, 
  GraphSat tc -> legal_tag t1 -> Rtaggedgraph t1 t2 -> legal_tag t2.
Proof.
  intros. induction H1.
  + apply H0.
  + apply IHRtaggedgraph. destruct H1.
    pose proof RPropisLegal _ _ _ H H0 H1 H5 H2 H3.
    apply H6.
Qed.
           
End taggedgraph.
  
Lemma GraphSattotag (t : tag) : forall tc,
  GraphSat tc -> Rtaggedgraph tc NullTag t -> legal_tag tc t.
Proof.
  intros. inversion H0.
  + apply NullisLegal.
  + pose proof NullisLegal tc. pose proof RisLegal _ _ _ H H7 H0. apply H8.
Qed.

Lemma NullTagll : forall tc, exists ll, UnTagged tc NullTag ll.
Proof.
  Admitted.
  
Lemma ZeroFullTag : forall tc t ll, UnTagged tc t ll -> 
      length ll = 0 -> FullTag tc t.
Proof.
  intros.
  unfold FullTag. unfold UnTagged in H. intros.
Admitted.

Lemma ExistUnTagged : forall tc t ll, 
  GraphSat tc -> UnTagged tc t ll ->  0 < length ll -> 
  (exists x, In x ll /\ t x = None /\ ~ reachable (GraphGen tc) x (Reversebool x)).
Proof.
  intros. destruct ll.
  + simpl in H0.
Admitted.

Lemma Existstnext : forall tc t x, GraphSat tc ->
  legal_tag tc t -> checkV tc x -> t x = None -> 
  ~ reachable (GraphGen tc) x (Reversebool x) ->
  (exists tn, RProp tc t tn x).
Proof.
  intros.
Admitted.

Lemma Shortertn : forall tc t tn x ll, GraphSat tc ->
  legal_tag tc t -> checkV tc x -> t x = None -> 
  ~ reachable (GraphGen tc) x (Reversebool x) ->
  RProp tc t tn x -> UnTagged tc t ll -> 
  exists lln, UnTagged tc tn lln /\ length lln < length ll.
Proof.
Admitted.

Lemma TagExist : forall tc, 
  GraphSat tc -> (exists t, Rtaggedgraph tc NullTag t).
Proof.
  intros. pose proof NullTagll tc as [ll ?].
  revert H0. pose proof NullisLegal tc. revert H0.
  generalize NullTag. remember (length ll) as n. revert ll Heqn.
  strong_induction n.
  intros. destruct n.
  + symmetry in Heqn. pose proof ZeroFullTag _ _ _ H1 Heqn.
    exists t. pose proof fully_tagged _ _ H2. apply H3.
  + pose proof PeanoNat.Nat.lt_0_succ n. rewrite Heqn in H2.
    pose proof ExistUnTagged _ _ _ H H1 H2.
    destruct H3. destruct H3.
    pose proof H1 x. apply H5 in H3. destruct H3. destruct H4.
    clear H4. pose proof Existstnext _ _ _ H H0 H3 H6 H7. 
    destruct H4 as [tn ?].
    
    
    


Lemma lttoFull : forall tc t,
  GraphSat tc -> Rtaggedgraph tc NullTag t -> FullTag tc t.
Proof.
  intros. induction H0.
  + apply H0.
  + apply IHRtaggedgraph.
Qed.

Lemma des_fst_lit (l1 l2 : lit) :
  fst l1 = fst l2 -> l1 = l2 \/ l1 = Reversebool l2.
Proof.
  intros.
  case l1, l2. simpl in H. rewrite H.
  case b0, b2. 
  + left. reflexivity.
  + unfold Reversebool. simpl.
    right. reflexivity.
  + unfold Reversebool. simpl.
    right. reflexivity.
  + left. reflexivity.
Qed.

Lemma lbothTF (tc : twoCNF) (l : lit) (inj : injec)  :
  checkV tc l -> cnftrue inj tc -> ~(liteval inj l = true /\ liteval inj (Reversebool l) = true).
Proof.
  intros. apply or_not_and.
  unfold cnftrue in H0. unfold cleval in H0.
  unfold checkV in H. destruct H.
  specialize (H0 x). destruct H. destruct H1.
  + apply des_fst_lit in H1. destruct H1.
    - rewrite H1 in H0. pose proof H0 H.
      generalize H2. unfold orb. rewrite <- neg_Reverselit.
      case (liteval inj l).
      * intros. right. apply diff_false_true.
      * intros. left. apply diff_false_true. 
    - rewrite H1 in H0. pose proof H0 H.
      generalize H2. unfold orb. rewrite <- neg_Reverselit.
      case (liteval inj l).
      * intros. right. simpl. apply diff_false_true.
      * intros. left. apply diff_false_true.
  + apply des_fst_lit in H1. destruct H1.
    - rewrite H1 in H0. pose proof H0 H.
      generalize H2. unfold orb. rewrite <- neg_Reverselit.
      case (liteval inj l).
      * intros. right. simpl. apply diff_false_true.
      * intros. left. apply diff_false_true.
    - rewrite H1 in H0. pose proof H0 H.
      generalize H2. unfold orb. rewrite <- neg_Reverselit.
      case (liteval inj l).
      * intros. right. simpl. apply diff_false_true.
      * intros. left. apply diff_false_true.
Qed.

Lemma nil_GraphSat: GraphSat nil.
Proof.
  unfold GraphSat. intros. apply not_checkVnill in H. congruence.
Qed.

Lemma nil_cnftrue: forall inj, cnftrue inj nil.
Proof.
  unfold cnftrue. intros. simpl in H. eapply False_ind. apply H.
Qed.
  
Lemma TsatToScc: forall tc,(exists inj, cnftrue inj tc) <-> GraphSat tc.
Proof.
  split.
  + intros. induction H. unfold GraphSat. intros.
    pose proof lbothTF _ _ _ H0 H.
    - apply or_not_and. apply not_and_or in H1.
      destruct H1.
      * right. unfold "~". intros. apply reach_eq_nece in H2.
        unfold necessary in H2. specialize (H2 x).
        apply H2 in H. 
        { rewrite H in H1. apply H1. reflexivity. }
        { pose proof Reverse_checkV tc l. apply H3. apply H0. }
        { apply H0. } { rewrite <- neg_Reverselit. apply negb_true_iff.
          apply not_true_is_false in H1. apply H1. }
        { pose proof Reverse_checkV tc l. apply H4. apply H0. }
        { apply H0. }
      * left. unfold "~". intros. apply reach_eq_nece in H2.
        unfold necessary in H2. specialize (H2 x).
        apply H2 in H.
        { rewrite H in H1. apply H1. reflexivity. }
        { apply H0. } { pose proof Reverse_checkV tc l. apply H3. apply H0. }
        { apply not_true_is_false in H1. 
          rewrite <- neg_Reverselit in H1. apply negb_false_iff.
          rewrite H1. reflexivity. } { apply H0. }
        { pose proof Reverse_checkV tc l. apply H4. apply H0. }
  + intros. pose proof GraphSattotag NullTag _ H. pose proof lttoFull.
      