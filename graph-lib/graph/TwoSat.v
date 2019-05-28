Axiom Classic : forall P : Prop, {P} + {~P}.

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

Lemma Re_Re : forall l, Reversebool (Reversebool l) = l.
Proof.
  intros. case l. intros. case b0.
  + unfold Reversebool. simpl. reflexivity.
  + unfold Reversebool. simpl. reflexivity.
Qed.

Lemma Reverse_checkE : forall e x y, checkE e ->
  st e = x -> ed e = y -> 
  checkE (fst e, negb (snd e)) /\ 
  st (fst e, negb (snd e)) = (Reversebool y) /\
  ed (fst e, negb (snd e)) = (Reversebool x).
Proof.
  intros. unfold checkE in H. unfold checkE. simpl.
  split. apply H.
  unfold st in H0. unfold st.
  unfold ed in H1. unfold ed.
  simpl. destruct e. destruct b.
  + simpl. simpl in H0. simpl in H1. split.
    - rewrite H1. reflexivity.
    - rewrite <- H0. rewrite Re_Re. reflexivity.
  + simpl. simpl in H0. simpl in H1. split.
    - rewrite H1. reflexivity.
    - rewrite <- H0. rewrite Re_Re. reflexivity.
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

Lemma checkV_l : forall tc a l, 
  checkV tc l -> checkV (a :: tc) l.
Proof.
  intros. unfold checkV in H. destruct H. exists x.
  split. destruct H. simpl. right. apply H.
  destruct H. apply H0.
Qed.
  
Lemma checkV_r : forall tc l l1 l2,
  checkV ((l1, l2) :: tc) l -> fst l <> fst l1 -> 
  fst l <> fst l2 -> checkV tc l.
Proof.
  intros. unfold checkV in H. destruct H. destruct H.
  simpl in H. destruct H2.
  + destruct H. 
    - rewrite <- H in H2. simpl in H2. congruence.
    - unfold checkV. exists x. split. apply H. left. apply H2.
  + destruct H.
    - rewrite <- H in H2. simpl in H2. congruence.
    - unfold checkV. exists x. split. apply H. right. apply H2.
Qed.

Lemma not_checkVnill : forall l, checkV nil l -> False.
Proof.
  intros.
  unfold checkV in H. destruct H.
  destruct H. simpl in H. apply H.
Qed.

Lemma reach_eq_nece: forall l1 l2 tc, checkV tc l1 -> checkV tc l2 -> 
  (reachable (GraphGen tc) l1 l2 -> necessary tc l1 l2).
Proof.
  intros. rewrite reachable_ind_reachable in H1.
    induction H1.
    - unfold necessary. intros. apply H5.
    - destruct H1. destruct H3. destruct H4.
      simpl in H5, H6. pose proof IHreachable H3 H0.
      unfold necessary. intros.
      pose proof H7 _ H8 H3 H0. apply H12. clear H12.
      rewrite <- H5 in H11. rewrite <- H6.
      rewrite <- H11. simpl in H4. unfold checkE in H4. 
      destruct e. simpl in H4.
      unfold st, ed. simpl. destruct b eqn:HHb.
      * unfold cnftrue in H8. pose proof H8 (nthcl tc n).
        eapply nth_In in H4. apply H12 in H4.
        unfold cleval in H4. apply orb_true_iff in H4.
        unfold st in H11. simpl in H11.
        destruct H4.
        { rewrite <- neg_Reverselit in H11.
          apply negb_true_iff in H11. rewrite H11 in H4.
          congruence. }
        { rewrite H4. rewrite H11. reflexivity. }
      * unfold cnftrue in H8. pose proof H8 (nthcl tc n).
        eapply nth_In in H4. apply H12 in H4.
        unfold cleval in H4. apply orb_true_iff in H4.
        unfold st in H11. simpl in H11.
        destruct H4.
        { rewrite H11. rewrite H4. reflexivity. }
        { rewrite <- neg_Reverselit in H11.
          apply negb_true_iff in H11. rewrite H11 in H4.
          congruence. }
Qed.
End Proof0.

Definition GraphSat (tc : twoCNF) : Prop :=
  forall l, checkV tc l ->
  ~(reachable (GraphGen tc) l (Reversebool l) 
  /\ reachable (GraphGen tc) (Reversebool l) l).
  
Lemma ReverseEdge: forall l1 l2 tc, 
  checkV tc l1 -> checkV tc l2 -> reachable (GraphGen tc) l1 l2 ->
  reachable (GraphGen tc) (Reversebool l2) (Reversebool l1).
Proof.
  intros.
  pose proof Reverse_checkV tc l1. apply H2 in H.
  pose proof Reverse_checkV tc l2. apply H3 in H0.
  rewrite reachable_ind_reachable in H1. induction H1.
  + rewrite reachable_ind_reachable. apply ind.reachable_nil.
    simpl. apply H.
  + destruct H1. destruct H5. simpl in H5.
    pose proof Reverse_checkV tc y. apply H7 in H5.
    pose proof IHreachable H5 H0 H7 H3.
    destruct H6. simpl in H9, H10, H6.
    pose proof Reverse_checkE _ _ _ _ H6 H9 H10.
    destruct H11. destruct H12.
    pose proof step_intro (GraphGen tc) _ _ _ H11 H12 H13.
    rewrite reachable_ind2_reachable in H8.
    assert ( HH : (GraphGen tc) |= (Reversebool y) ~> (Reversebool x) ).
    split. apply H5. split. apply H. apply H14.
    pose proof ind2.reachable_cons (GraphGen tc) _ _ _ H8 HH.
    rewrite reachable_ind2_reachable. apply H15.
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
  NoDup ll /\ forall l, In l ll <-> (checkV tc l /\ t l = None).

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

Lemma None_eq : forall l1 l2 t, legal_tag t -> 
  checkV tc l1 -> checkV tc l2 ->
  fst l1 = fst l2 -> t l1 = None -> t l2 = None.
Proof.
  intros. destruct l1. destruct l2. simpl in H2.
  destruct b0.
  + destruct b2. rewrite <- H2. apply H3. rewrite <- H2.
    pose proof ReverseNoneTag _ _ H H0 H3. 
    unfold Reversebool in H4. simpl in H4. apply H4.
  + destruct b2. rewrite <- H2.
    pose proof ReverseNoneTag _ _ H H0 H3.
    unfold Reversebool in H4. simpl in H4. apply H4.
    rewrite <- H2. apply H3.
Qed.

Lemma tag_ueq : forall (t : tag) l1 l2 b, legal_tag t -> 
  checkV tc l1 -> checkV tc l2 -> 
  t l1 = None -> t l2 = Some b -> fst l1 <> fst l2.
Proof.
  intros.
  unfold not. intros. pose proof None_eq _ _ _ H H0 H1 H4 H2.
  rewrite H3 in H5. congruence.
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
  + apply IHRtaggedgraph. rename H0 into lt. destruct H1.
    pose proof RPropisLegal _ _ _ H lt H0 H1 H2 H3.
    apply H5.
Qed.
           
End taggedgraph.
  
Lemma GraphSattotag (t : tag) : forall tc,
  GraphSat tc -> Rtaggedgraph tc NullTag t -> legal_tag tc t.
Proof.
  intros. inversion H0.
  + apply NullisLegal.
  + pose proof NullisLegal tc. pose proof RisLegal _ _ _ H H7 H0. apply H8.
Qed.

Lemma NullTagll : forall tc ll, 
  (forall l, checkV tc l <-> In l ll) -> NoDup ll ->
  UnTagged tc NullTag ll.
Proof.
  intros. unfold UnTagged. split. auto. clear H0.
  intros. split.
  + intros. split.
    - pose proof H l. apply H1. apply H0.
    - unfold NullTag. reflexivity.
  + intros. destruct H0. pose proof H l.
    apply H2 in H0. apply H0.
Qed.

Lemma AddEle : forall l1 l2 (a : lit), NoDup l2 ->
  (forall x, In x l1 <-> In x l2) ->
  (exists l3, NoDup l3 /\
  (forall x, In x (a :: l1) <-> In x l3)).
Proof.
  intros. assert ( Hin : In a l2 \/ ~ In a l2 ).
  apply classic. destruct Hin.
  + exists l2. split. auto. intros. split.
    - intros. unfold In in H2. destruct H2.
      * rewrite <- H2. apply H1.
      * pose proof H0 x. apply H3 in H2. apply H2.
    - intros. pose proof H0 x. apply H3 in H2.
      unfold In. right. apply H2.
  + exists (a :: l2). split.
    pose proof NoDup_cons _ H1 H. apply H2.
    intros. split.
    - intros. destruct H2.
      * rewrite H2. simpl. left. reflexivity.
      * pose proof H0 x. apply H3 in H2.
        simpl. right. apply H2.
    - intros. destruct H2.
      * rewrite H2. simpl. left. reflexivity.
      * pose proof H0 x. apply H3 in H2.
        simpl. right. apply H2.
Qed.

Lemma AddEleP : forall l1 l2 (a : lit) (P : Prop), NoDup l2 ->
  P -> (forall x, In x l1 <-> In x l2) ->
  (exists l3, NoDup l3 /\
  (forall x, In x (a :: l1) <-> In x l3)).
(*
  (forall x, ((P /\ In x (a :: l1)) \/ (~P /\ In x l1)) <-> In x l3)). *)
Proof.
  intros l1 l2 a P H Hp H0. assert ( Hin : In a l2 \/ ~ In a l2 ). apply classic.
  destruct Hin.
  + exists l2. split. auto. intros. split.
    - intros. unfold In in H2. destruct H2.
      * rewrite <- H2. apply H1.
      * pose proof H0 x. apply H3 in H2. apply H2.
    - intros. pose proof H0 x. apply H3 in H2.
      unfold In. right. apply H2.
  + exists (a :: l2). split.
    pose proof NoDup_cons _ H1 H. apply H2.
    intros. split.
    - intros. destruct H2.
      * rewrite H2. simpl. left. reflexivity.
      * pose proof H0 x. apply H3 in H2.
        simpl. right. apply H2.
    - intros. destruct H2.
      * rewrite H2. simpl. left. reflexivity.
      * pose proof H0 x. apply H3 in H2.
        simpl. right. apply H2.
Qed.

Lemma AddEleP' : forall (l1 l2 : list lit) (a : lit) (P : Prop), NoDup l2 ->
  (~P) -> (forall x, In x l1 <-> In x l2) ->
  (exists l3, NoDup l3 /\
  (forall x, In x l1 <-> In x l3)).
(*
  (forall x, ((P /\ In x (a :: l1)) \/ (~P /\ In x l1)) <-> In x l3)). *)
Proof.
  intros l1 l2 a P H Hp H0. assert ( Hin : In a l2 \/ ~ In a l2 ). apply classic.
  destruct Hin.
  + exists l2. split. auto. auto.
  + exists l2. split. auto. auto.
Qed.

(*
  + exists l2. split. auto. intros. split.
    - intros. unfold In in H2. destruct H2.
      * destruct H2. rewrite H0 in H3. destruct H3.
        rewrite <- H3. apply H1. apply H3.
      * pose proof H0 x. destruct H2. apply H3 in H4. apply H4.
    - intros. pose proof H0 x. apply H3 in H2.
      destruct Hp.
      * left. split. apply H4. unfold In. right. apply H2.
      * right. split. apply H4. apply H2.
  + destruct Hp.
    - exists (a :: l2). split. 
      pose proof NoDup_cons _ H1 H. apply H3.
      intros. split.
      * intros. destruct H3.
        ++ destruct H3. destruct H4. simpl. left. apply H4.
           apply H0 in H4. simpl. right. apply H4.
        ++ destruct H3. congruence.
      * intros. left. split. apply H2. destruct H3.
        ++ simpl. left. apply H3.
        ++ simpl. right. apply H0. apply H3.
    - exists l2. split. apply H. intros. split.
      * intros. destruct H3. 
        ++ destruct H3. congruence.
        ++ destruct H3. apply H0. apply H4.
      * intros. right. split. apply H2. apply H0. apply H3.
Qed. *)

Fixpoint tclist (tc : twoCNF) : list lit :=
  match tc with
  | nil => nil
  | c :: tc' => (fst (fst c), true) :: (fst (fst c), false) ::(fst (snd c), true) :: (fst (snd c), false) :: tclist tc'
  end.

Lemma checkV2tclist : forall tc l,
  checkV tc l <-> In l (tclist tc).
Proof.
  intros. split. 
  + intros. unfold checkV in H. destruct H. 
    destruct H. destruct H0.
    - induction tc.
      * simpl. simpl in H. apply H.
      * simpl. induction H.
        ++ destruct (snd l) eqn:HH0.
           -- rewrite <- H in H0. left. rewrite H0.
              rewrite <- HH0. rewrite surjective_pairing.
              reflexivity.
           -- rewrite <- H in H0. right. left.
              rewrite H0. rewrite <- HH0.
              rewrite surjective_pairing. reflexivity.
        ++ right. right. right. right. apply IHtc in H. apply H.
    - induction tc.
      * simpl. simpl in H. apply H.
      * simpl. induction H.
        ++ destruct (snd l) eqn:HH0.
           -- rewrite <- H in H0. right. right. left. rewrite H0.
              rewrite <- HH0. rewrite surjective_pairing.
              reflexivity.
           -- rewrite <- H in H0. right. right. right. left.
              rewrite H0. rewrite <- HH0.
              rewrite surjective_pairing. reflexivity.
        ++ right. right. right. right. apply IHtc in H. apply H.
  + intros. unfold checkV. induction tc.
    - simpl in H. contradiction.
    - destruct H.
      * exists a. split. simpl. left. reflexivity.
        left. rewrite <- H. simpl. reflexivity.
      * destruct H.
        ++ exists a. split. simpl. left. reflexivity.
           left. rewrite <- H. simpl. reflexivity.
        ++ destruct H.
           -- exists a. split. simpl. left. reflexivity.
              right. rewrite <- H. simpl. reflexivity.
           -- destruct H.
              ** exists a. split. simpl. left. reflexivity.
                 right. rewrite <- H. simpl. reflexivity.
              ** apply IHtc in H. destruct H. destruct H.
                 exists x. split. simpl. right. apply H.
                 apply H0.
Qed.
        
Lemma NullTagllexists : 
  forall tc, exists ll, UnTagged tc NullTag ll.
Proof.
  intros. 
  assert ( H : exists ll, NoDup ll /\ forall l, checkV tc l <-> In l ll ).
  + induction tc.
    - exists nil. split. constructor. intros. split.
      * intros. simpl. unfold checkV in H. destruct H.
        destruct H. simpl in H. apply H.
      * intros. simpl in H. contradiction.
    - destruct IHtc. destruct H. destruct a.
      pose proof checkV2tclist tc.
      assert (H01 : forall l : lit, In l (tclist tc) <-> In l x).
      intros. rewrite <- H0. rewrite <- H1. apply iff_refl.
      pose proof AddEle (tclist tc) x (fst l0, false) H H01.
      destruct H2. destruct H2.
      pose proof AddEle ((fst l0, false) :: tclist tc) x0 (fst l0, true) H2 H3.
      destruct H4. destruct H4.
      pose proof AddEle ((fst l0, true) :: (fst l0, false) :: tclist tc) x1 (fst l, false) H4 H5.
      destruct H6. destruct H6.
      pose proof AddEle ((fst l, false) :: (fst l0, true) :: (fst l0, false) :: tclist tc) x2 (fst l, true) H6 H7.
      destruct H8. exists x3. destruct H8.
      split. apply H8. intros.
      pose proof checkV2tclist ((l, l0) :: tc) l1.
      rewrite H10. pose proof H9 l1. apply H11.
  + destruct H. destruct H. exists x.
    unfold UnTagged. split. apply H.
    split.
    - intros. apply H0 in H1. split. apply H1. unfold NullTag.
      reflexivity.
    - intros. destruct H1. apply H0 in H1. apply H1.
Qed.

Lemma fst2all : forall (l1 l2 : lit), l1 <> (fst l2, true) -> l1 <> (fst l2, false) -> fst l1 <> fst l2.
Proof.
  intros. unfold not. intros. rewrite <- H1 in H.
  rewrite <- H1 in H0. destruct l1. destruct b0.
  + simpl in H. congruence.
  + simpl in H0. congruence.
Qed.

Lemma Nonediff : forall (t : tag) l1 l2 b, t l1 = None -> t l2 = Some b -> l1 <> l2.
Proof.
  intros. unfold not. intros. rewrite H1 in H. rewrite H in H0.
  congruence.
Qed.

Lemma LegalTagllexists : 
  forall tc t, exists ll, UnTagged tc t ll.
Proof.
  intros.
  assert ( H : exists ll, NoDup ll /\ forall l, (t l = None /\ checkV tc l) <-> In l ll ).
  + induction tc.
    - exists nil. split. constructor. intros. split.
      * intros. simpl. unfold checkV in H. destruct H.
        destruct H0. simpl in H0. apply H0.
      * intros. simpl in H. contradiction.
    - destruct IHtc.
      destruct H. destruct a.
      assert (H01 : forall l : lit, In l x <-> In l x).
      intros. reflexivity.
      destruct (t (fst l0, false)) eqn:HH0f.
      { destruct (t (fst l0, true)) eqn:HH0t. 
        { destruct (t (fst l, false)) eqn:HHf.
          { destruct (t (fst l, true)) eqn:HHt.
            { exists x. split. apply H. intros. split.
              intros. apply H0. destruct H1. split. apply H1.
              pose proof Nonediff _ _ _ _ H1 HH0f.
              pose proof Nonediff _ _ _ _ H1 HH0t.
              pose proof Nonediff _ _ _ _ H1 HHf.
              pose proof Nonediff _ _ _ _ H1 HHt.
              pose proof fst2all _ _ H4 H3.
              pose proof fst2all _ _ H6 H5.
              pose proof checkV_r _ _ _ _ H2 H8 H7. apply H9.
              intros. apply H0 in H1. destruct H1. split.
              apply H1. pose proof checkV_l _ (l, l0) _ H2.
              apply H3. }
            { pose proof AddEleP x x (fst l, true) (t (fst l, true) = None) H HHt H01.
              destruct H1. destruct H1.
              exists x0. split. apply H1. intros. split.
              intros. apply H2. simpl.
              assert ( l1 = (fst l, true) \/ l1 <> (fst l, true) ). apply classic. destruct H4.
              left. rewrite H4. auto. right.
              apply H0. destruct H3. split. apply H3.
              pose proof Nonediff _ _ _ _ H3 HH0f.
              pose proof Nonediff _ _ _ _ H3 HH0t.
              pose proof Nonediff _ _ _ _ H3 HHf.
              pose proof fst2all _ _ H7 H6.
              pose proof fst2all _ _ H4 H8.
              pose proof checkV_r _ _ _ _ H5 H10 H9. apply H11.
              intros. rewrite <- H2 in H3. destruct H3. split.
              rewrite H3 in HHt. apply HHt. unfold checkV.
              exists (l, l0). split. simpl. left. auto.
              simpl. left. rewrite <- H3. simpl. auto.
              apply H0 in H3. destruct H3. split.
              apply H3. pose proof checkV_l _ (l, l0) _ H4.
              apply H5. } }
          { destruct (t (fst l, true)) eqn:HHt.
            { pose proof AddEleP x x (fst l, false) (t (fst l, false) = None) H HHf H01.
              destruct H1. destruct H1.
              exists x0. split. apply H1. intros. split.
              intros. apply H2. simpl.
              assert ( l1 = (fst l, false) \/ l1 <> (fst l, false) ). apply classic. destruct H4.
              left. rewrite H4. auto. right.
              apply H0. destruct H3. split. apply H3.
              pose proof Nonediff _ _ _ _ H3 HH0f.
              pose proof Nonediff _ _ _ _ H3 HH0t.
              pose proof Nonediff _ _ _ _ H3 HHt.
              pose proof fst2all _ _ H7 H6.
              pose proof fst2all _ _ H8 H4.
              pose proof checkV_r _ _ _ _ H5 H10 H9. apply H11.
              intros. rewrite <- H2 in H3. destruct H3. split.
              rewrite H3 in HHf. apply HHf. unfold checkV.
              exists (l, l0). split. simpl. left. auto.
              simpl. left. rewrite <- H3. simpl. auto.
              apply H0 in H3. destruct H3. split.
              apply H3. pose proof checkV_l _ (l, l0) _ H4.
              apply H5. }
            { pose proof AddEleP x x (fst l, false) (t (fst l, false) = None) H HHf H01.
              destruct H1. destruct H1.
              pose proof AddEleP ((fst l, false) :: x) x0 (fst l, true) (t (fst l, true) = None) H1 HHt H2.
              destruct H3. destruct H3.
              exists x1. split. apply H3. intros. split.
              intros. apply H4. simpl.
              assert ( l1 = (fst l, true) \/ l1 <> (fst l, true) ). apply classic. destruct H6. rewrite H6. auto. right.
              assert ( l1 = (fst l, false) \/ l1 <> (fst l, false) ). apply classic. destruct H7. rewrite H7. auto. right.
              apply H0. destruct H5. split. apply H5. 
              pose proof Nonediff _ _ _ _ H5 HH0f.
              pose proof Nonediff _ _ _ _ H5 HH0t.
              pose proof fst2all _ _ H6 H7.
              pose proof fst2all _ _ H10 H9.
              pose proof checkV_r _ _ _ _ H8 H11 H12. apply H13.
              intros. rewrite <- H4 in H5. destruct H5. split.
              rewrite <- H5. apply HHt. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl.
              rewrite <- H5. simpl. left. auto. destruct H5.
              split. rewrite <- H5. apply HHf. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl. 
              rewrite <- H5. simpl. left. auto. apply H0 in H5.
              destruct H5. split. apply H5.
              pose proof checkV_l _ (l, l0) _ H6. apply H7. } } }
        { destruct (t (fst l, false)) eqn:HHf.
          { destruct (t (fst l, true)) eqn:HHt.
            { pose proof AddEleP x x (fst l0, true) (t (fst l0, true) = None) H HH0t H01.
              destruct H1. destruct H1.
              exists x0. split. apply H1. intros. split.
              intros. apply H2. simpl.
              assert ( l1 = (fst l0, true) \/ l1 <> (fst l0, true) ). apply classic. destruct H4.
              left. rewrite H4. auto. right.
              apply H0. destruct H3. split. apply H3.
              pose proof Nonediff _ _ _ _ H3 HHf.
              pose proof Nonediff _ _ _ _ H3 HHt.
              pose proof Nonediff _ _ _ _ H3 HH0f.
              pose proof fst2all _ _ H7 H6.
              pose proof fst2all _ _ H4 H8.
              pose proof checkV_r _ _ _ _ H5 H9 H10. apply H11.
              intros. rewrite <- H2 in H3. destruct H3. split.
              rewrite H3 in HH0t. apply HH0t. unfold checkV.
              exists (l, l0). split. simpl. left. auto.
              simpl. right. rewrite <- H3. simpl. auto.
              apply H0 in H3. destruct H3. split.
              apply H3. pose proof checkV_l _ (l, l0) _ H4.
              apply H5. }
            { pose proof AddEleP x x (fst l0, true) (t (fst l0, true) = None) H HH0t H01.
              destruct H1. destruct H1.
              pose proof AddEleP ((fst l0, true) :: x) x0 (fst l, true) (t (fst l, true) = None) H1 HHt H2.
              destruct H3. destruct H3.
              exists x1. split. apply H3. intros. split.
              intros. apply H4. simpl.
              assert ( l1 = (fst l, true) \/ l1 <> (fst l, true) ). apply classic. destruct H6. rewrite H6. auto. right.
              assert ( l1 = (fst l0, true) \/ l1 <> (fst l0, true) ). apply classic. destruct H7. rewrite H7. auto. right.
              apply H0. destruct H5. split. apply H5. 
              pose proof Nonediff _ _ _ _ H5 HH0f.
              pose proof Nonediff _ _ _ _ H5 HHf.
              pose proof fst2all _ _ H6 H10.
              pose proof fst2all _ _ H7 H9.
              pose proof checkV_r _ _ _ _ H8 H11 H12. apply H13.
              intros. rewrite <- H4 in H5. destruct H5. split.
              rewrite <- H5. apply HHt. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl.
              rewrite <- H5. simpl. left. auto. destruct H5.
              split. rewrite <- H5. apply HH0t. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl. 
              rewrite <- H5. simpl. right. auto. apply H0 in H5.
              destruct H5. split. apply H5.
              pose proof checkV_l _ (l, l0) _ H6. apply H7. } }
          { destruct (t (fst l, true)) eqn:HHt.
            { pose proof AddEleP x x (fst l0, true) (t (fst l0, true) = None) H HH0t H01.
              destruct H1. destruct H1.
              pose proof AddEleP ((fst l0, true) :: x) x0 (fst l, false) (t (fst l, false) = None) H1 HHf H2.
              destruct H3. destruct H3.
              exists x1. split. apply H3. intros. split.
              intros. apply H4. simpl.
              assert ( l1 = (fst l, false) \/ l1 <> (fst l, false) ). apply classic. destruct H6. rewrite H6. auto. right.
              assert ( l1 = (fst l0, true) \/ l1 <> (fst l0, true) ). apply classic. destruct H7. rewrite H7. auto. right.
              apply H0. destruct H5. split. apply H5. 
              pose proof Nonediff _ _ _ _ H5 HH0f.
              pose proof Nonediff _ _ _ _ H5 HHt.
              pose proof fst2all _ _ H10 H6.
              pose proof fst2all _ _ H7 H9.
              pose proof checkV_r _ _ _ _ H8 H11 H12. apply H13.
              intros. rewrite <- H4 in H5. destruct H5. split.
              rewrite <- H5. apply HHf. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl.
              rewrite <- H5. simpl. left. auto. destruct H5.
              split. rewrite <- H5. apply HH0t. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl. 
              rewrite <- H5. simpl. right. auto. apply H0 in H5.
              destruct H5. split. apply H5.
              pose proof checkV_l _ (l, l0) _ H6. apply H7. }
            { pose proof AddEleP x x (fst l0, true) (t (fst l0, true) = None) H HH0t H01.
              destruct H1. destruct H1.
              pose proof AddEleP ((fst l0, true) :: x) x0 (fst l, false) (t (fst l, false) = None) H1 HHf H2.
              destruct H3. destruct H3.
              pose proof AddEleP ((fst l, false) :: (fst l0, true) :: x) x1 (fst l, true) (t (fst l, true) = None) H3 HHt H4.
              destruct H5. destruct H5.
              exists x2. split. apply H5. intros. split.
              intros. apply H6. simpl.
              assert ( l1 = (fst l, true) \/ l1 <> (fst l, true) ). apply classic. destruct H8. rewrite H8. auto. right.
              assert ( l1 = (fst l, false) \/ l1 <> (fst l, false) ). apply classic. destruct H9. rewrite H9. auto. right.
              assert ( l1 = (fst l0, true) \/ l1 <> (fst l0, true) ). apply classic. destruct H10. rewrite H10. auto. right.
              apply H0. destruct H7. split. apply H7. 
              pose proof Nonediff _ _ _ _ H7 HH0f.
              pose proof fst2all _ _ H8 H9.
              pose proof fst2all _ _ H10 H12.
              pose proof checkV_r _ _ _ _ H11 H13 H14. apply H15.
              intros. rewrite <- H6 in H7. destruct H7. split.
              rewrite <- H7. apply HHt. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl.
              rewrite <- H7. simpl. left. auto. destruct H7.
              split. rewrite <- H7. apply HHf. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl. 
              rewrite <- H7. simpl. left. auto. destruct H7.
              split. rewrite <- H7. apply HH0t. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl.
              rewrite <- H7. simpl. right. auto. apply H0 in H7.
              destruct H7. split. apply H7.
              pose proof checkV_l _ (l, l0) _ H8. apply H9. } } } }
      { destruct (t (fst l0, true)) eqn:HH0t. 
        { destruct (t (fst l, false)) eqn:HHf.
          { destruct (t (fst l, true)) eqn:HHt.
            { pose proof AddEleP x x (fst l0, false) (t (fst l0, false) = None) H HH0f H01.
              destruct H1. destruct H1.
              exists x0. split. apply H1. intros. split.
              intros. apply H2. simpl.
              assert ( l1 = (fst l0, false) \/ l1 <> (fst l0, false) ). apply classic. destruct H4.
              left. rewrite H4. auto. right.
              apply H0. destruct H3. split. apply H3.
              pose proof Nonediff _ _ _ _ H3 HH0t.
              pose proof Nonediff _ _ _ _ H3 HHt.
              pose proof Nonediff _ _ _ _ H3 HHf.
              pose proof fst2all _ _ H7 H8.
              pose proof fst2all _ _ H6 H4.
              pose proof checkV_r _ _ _ _ H5 H9 H10. apply H11.
              intros. rewrite <- H2 in H3. destruct H3. split.
              rewrite H3 in HH0f. apply HH0f. unfold checkV.
              exists (l, l0). split. simpl. left. auto.
              simpl. right. rewrite <- H3. simpl. auto.
              apply H0 in H3. destruct H3. split.
              apply H3. pose proof checkV_l _ (l, l0) _ H4.
              apply H5. }
            { pose proof AddEleP x x (fst l0, false) (t (fst l0, false) = None) H HH0f H01.
              destruct H1. destruct H1.
              pose proof AddEleP ((fst l0, false) :: x) x0 (fst l, true) (t (fst l, true) = None) H1 HHt H2.
              destruct H3. destruct H3.
              exists x1. split. apply H3. intros. split.
              intros. apply H4. simpl.
              assert ( l1 = (fst l, true) \/ l1 <> (fst l, true) ). apply classic. destruct H6. rewrite H6. auto. right.
              assert ( l1 = (fst l0, false) \/ l1 <> (fst l0, false) ). apply classic. destruct H7. rewrite H7. auto. right.
              apply H0. destruct H5. split. apply H5. 
              pose proof Nonediff _ _ _ _ H5 HH0t.
              pose proof Nonediff _ _ _ _ H5 HHf.
              pose proof fst2all _ _ H6 H10.
              pose proof fst2all _ _ H9 H7.
              pose proof checkV_r _ _ _ _ H8 H11 H12. apply H13.
              intros. rewrite <- H4 in H5. destruct H5. split.
              rewrite <- H5. apply HHt. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl.
              rewrite <- H5. simpl. left. auto. destruct H5.
              split. rewrite <- H5. apply HH0f. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl. 
              rewrite <- H5. simpl. right. auto. apply H0 in H5.
              destruct H5. split. apply H5.
              pose proof checkV_l _ (l, l0) _ H6. apply H7. } }
          { destruct (t (fst l, true)) eqn:HHt.
            { pose proof AddEleP x x (fst l0, false) (t (fst l0, false) = None) H HH0f H01.
              destruct H1. destruct H1.
              pose proof AddEleP ((fst l0, false) :: x) x0 (fst l, false) (t (fst l, false) = None) H1 HHf H2.
              destruct H3. destruct H3.
              exists x1. split. apply H3. intros. split.
              intros. apply H4. simpl.
              assert ( l1 = (fst l, false) \/ l1 <> (fst l, false) ). apply classic. destruct H6. rewrite H6. auto. right.
              assert ( l1 = (fst l0, false) \/ l1 <> (fst l0, false) ). apply classic. destruct H7. rewrite H7. auto. right.
              apply H0. destruct H5. split. apply H5. 
              pose proof Nonediff _ _ _ _ H5 HH0t.
              pose proof Nonediff _ _ _ _ H5 HHt.
              pose proof fst2all _ _ H10 H6.
              pose proof fst2all _ _ H9 H7.
              pose proof checkV_r _ _ _ _ H8 H11 H12. apply H13.
              intros. rewrite <- H4 in H5. destruct H5. split.
              rewrite <- H5. apply HHf. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl.
              rewrite <- H5. simpl. left. auto. destruct H5.
              split. rewrite <- H5. apply HH0f. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl. 
              rewrite <- H5. simpl. right. auto. apply H0 in H5.
              destruct H5. split. apply H5.
              pose proof checkV_l _ (l, l0) _ H6. apply H7. }
            { pose proof AddEleP x x (fst l0, false) (t (fst l0, false) = None) H HH0f H01.
              destruct H1. destruct H1.
              pose proof AddEleP ((fst l0, false) :: x) x0 (fst l, false) (t (fst l, false) = None) H1 HHf H2.
              destruct H3. destruct H3.
              pose proof AddEleP ((fst l, false) :: (fst l0, false) :: x) x1 (fst l, true) (t (fst l, true) = None) H3 HHt H4.
              destruct H5. destruct H5.
              exists x2. split. apply H5. intros. split.
              intros. apply H6. simpl.
              assert ( l1 = (fst l, true) \/ l1 <> (fst l, true) ). apply classic. destruct H8. rewrite H8. auto. right.
              assert ( l1 = (fst l, false) \/ l1 <> (fst l, false) ). apply classic. destruct H9. rewrite H9. auto. right.
              assert ( l1 = (fst l0, false) \/ l1 <> (fst l0, false) ). apply classic. destruct H10. rewrite H10. auto. right.
              apply H0. destruct H7. split. apply H7. 
              pose proof Nonediff _ _ _ _ H7 HH0t.
              pose proof fst2all _ _ H8 H9.
              pose proof fst2all _ _ H12 H10.
              pose proof checkV_r _ _ _ _ H11 H13 H14. apply H15.
              intros. rewrite <- H6 in H7. destruct H7. split.
              rewrite <- H7. apply HHt. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl.
              rewrite <- H7. simpl. left. auto. destruct H7.
              split. rewrite <- H7. apply HHf. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl. 
              rewrite <- H7. simpl. left. auto. destruct H7.
              split. rewrite <- H7. apply HH0f. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl.
              rewrite <- H7. simpl. right. auto. apply H0 in H7.
              destruct H7. split. apply H7.
              pose proof checkV_l _ (l, l0) _ H8. apply H9. } } }
        { destruct (t (fst l, false)) eqn:HHf.
          { destruct (t (fst l, true)) eqn:HHt.
            { pose proof AddEleP x x (fst l0, false) (t (fst l0, false) = None) H HH0f H01.
              destruct H1. destruct H1.
              pose proof AddEleP ((fst l0, false) :: x) x0 (fst l0, true) (t (fst l0, true) = None) H1 HH0t H2.
              destruct H3. destruct H3.
              exists x1. split. apply H3. intros. split.
              intros. apply H4. simpl.
              assert ( l1 = (fst l0, true) \/ l1 <> (fst l0, true) ). apply classic. destruct H6. rewrite H6. auto. right.
              assert ( l1 = (fst l0, false) \/ l1 <> (fst l0, false) ). apply classic. destruct H7. rewrite H7. auto. right.
              apply H0. destruct H5. split. apply H5. 
              pose proof Nonediff _ _ _ _ H5 HHt.
              pose proof Nonediff _ _ _ _ H5 HHf.
              pose proof fst2all _ _ H9 H10.
              pose proof fst2all _ _ H6 H7.
              pose proof checkV_r _ _ _ _ H8 H11 H12. apply H13.
              intros. rewrite <- H4 in H5. destruct H5. split.
              rewrite <- H5. apply HH0t. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl.
              rewrite <- H5. simpl. right. auto. destruct H5.
              split. rewrite <- H5. apply HH0f. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl. 
              rewrite <- H5. simpl. right. auto. apply H0 in H5.
              destruct H5. split. apply H5.
              pose proof checkV_l _ (l, l0) _ H6. apply H7. }
            { pose proof AddEleP x x (fst l0, false) (t (fst l0, false) = None) H HH0f H01.
              destruct H1. destruct H1.
              pose proof AddEleP ((fst l0, false) :: x) x0 (fst l0, true) (t (fst l0, true) = None) H1 HH0t H2.
              destruct H3. destruct H3.
              pose proof AddEleP ((fst l0, true) :: (fst l0, false) :: x) x1 (fst l, true) (t (fst l, true) = None) H3 HHt H4.
              destruct H5. destruct H5.
              exists x2. split. apply H5. intros. split.
              intros. apply H6. simpl.
              assert ( l1 = (fst l, true) \/ l1 <> (fst l, true) ). apply classic. destruct H8. rewrite H8. auto. right.
              assert ( l1 = (fst l0, true) \/ l1 <> (fst l0, true) ). apply classic. destruct H9. rewrite H9. auto. right.
              assert ( l1 = (fst l0, false) \/ l1 <> (fst l0, false) ). apply classic. destruct H10. rewrite H10. auto. right.
              apply H0. destruct H7. split. apply H7. 
              pose proof Nonediff _ _ _ _ H7 HHf.
              pose proof fst2all _ _ H8 H12.
              pose proof fst2all _ _ H9 H10.
              pose proof checkV_r _ _ _ _ H11 H13 H14. apply H15.
              intros. rewrite <- H6 in H7. destruct H7. split.
              rewrite <- H7. apply HHt. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl.
              rewrite <- H7. simpl. left. auto. destruct H7.
              split. rewrite <- H7. apply HH0t. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl. 
              rewrite <- H7. simpl. right. auto. destruct H7.
              split. rewrite <- H7. apply HH0f. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl.
              rewrite <- H7. simpl. right. auto. apply H0 in H7.
              destruct H7. split. apply H7.
              pose proof checkV_l _ (l, l0) _ H8. apply H9. } }
          { destruct (t (fst l, true)) eqn:HHt.
            { pose proof AddEleP x x (fst l0, false) (t (fst l0, false) = None) H HH0f H01.
              destruct H1. destruct H1.
              pose proof AddEleP ((fst l0, false) :: x) x0 (fst l0, true) (t (fst l0, true) = None) H1 HH0t H2.
              destruct H3. destruct H3.
              pose proof AddEleP ((fst l0, true) :: (fst l0, false) :: x) x1 (fst l, false) (t (fst l, false) = None) H3 HHf H4.
              destruct H5. destruct H5.
              exists x2. split. apply H5. intros. split.
              intros. apply H6. simpl.
              assert ( l1 = (fst l, false) \/ l1 <> (fst l, false) ). apply classic. destruct H8. rewrite H8. auto. right.
              assert ( l1 = (fst l0, true) \/ l1 <> (fst l0, true) ). apply classic. destruct H9. rewrite H9. auto. right.
              assert ( l1 = (fst l0, false) \/ l1 <> (fst l0, false) ). apply classic. destruct H10. rewrite H10. auto. right.
              apply H0. destruct H7. split. apply H7. 
              pose proof Nonediff _ _ _ _ H7 HHt.
              pose proof fst2all _ _ H12 H8.
              pose proof fst2all _ _ H9 H10.
              pose proof checkV_r _ _ _ _ H11 H13 H14. apply H15.
              intros. rewrite <- H6 in H7. destruct H7. split.
              rewrite <- H7. apply HHf. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl.
              rewrite <- H7. simpl. left. auto. destruct H7.
              split. rewrite <- H7. apply HH0t. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl. 
              rewrite <- H7. simpl. right. auto. destruct H7.
              split. rewrite <- H7. apply HH0f. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl.
              rewrite <- H7. simpl. right. auto. apply H0 in H7.
              destruct H7. split. apply H7.
              pose proof checkV_l _ (l, l0) _ H8. apply H9. }
            { pose proof AddEleP x x (fst l0, false) (t (fst l0, false) = None) H HH0f H01.
              destruct H1. destruct H1.
              pose proof AddEleP ((fst l0, false) :: x) x0 (fst l0, true) (t (fst l0, true) = None) H1 HH0t H2.
              destruct H3. destruct H3.
              pose proof AddEleP ((fst l0, true) :: (fst l0, false) :: x) x1 (fst l, false) (t (fst l, false) = None) H3 HHf H4.
              destruct H5. destruct H5.
              pose proof AddEleP ((fst l, false) :: (fst l0, true) :: (fst l0, false) :: x) x2 (fst l, true) (t (fst l, true) = None) H5 HHt H6.
              destruct H7. destruct H7.
              exists x3. split. apply H7. intros. split.
              intros. apply H8. simpl.
              assert ( l1 = (fst l, true) \/ l1 <> (fst l, true) ). apply classic. destruct H10. rewrite H10. auto. right.
              assert ( l1 = (fst l, false) \/ l1 <> (fst l, false) ). apply classic. destruct H11. rewrite H11. auto. right.
              assert ( l1 = (fst l0, true) \/ l1 <> (fst l0, true) ). apply classic. destruct H12. rewrite H12. auto. right.
              assert ( l1 = (fst l0, false) \/ l1 <> (fst l0, false) ). apply classic. destruct H13. rewrite H13. auto. right.
              apply H0. destruct H9. split. apply H9. 
              pose proof fst2all _ _ H10 H11.
              pose proof fst2all _ _ H12 H13.
              pose proof checkV_r _ _ _ _ H14 H15 H16. apply H17.
              intros. rewrite <- H8 in H9. destruct H9. split.
              rewrite <- H9. apply HHt. unfold checkV. 
              exists (l, l0). split. simpl. left. auto. simpl.
              rewrite <- H9. simpl. left. auto. destruct H9.
              split. rewrite <- H9. apply HHf. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl.
              rewrite <- H9. simpl. left. auto. destruct H9.
              split. rewrite <- H9. apply HH0t. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl. 
              rewrite <- H9. simpl. right. auto. destruct H9.
              split. rewrite <- H9. apply HH0f. unfold checkV.
              exists (l, l0). split. simpl. left. auto. simpl.
              rewrite <- H9. simpl. right. auto. apply H0 in H9.
              destruct H9. split. apply H9.
              pose proof checkV_l _ (l, l0) _ H10. apply H11. }}}}
  + destruct H. destruct H. exists x.
    unfold UnTagged. split. apply H.
    split.
    - intros. apply H0 in H1. destruct H1. apply (conj H2 H1). 
    - intros. destruct H1.
      pose proof proj1 (H0 l) (conj H2 H1). apply H3.
Qed.

Lemma ZeroFullTag : forall tc t ll, UnTagged tc t ll -> 
      length ll = 0 -> FullTag tc t.
Proof.
  intros. unfold UnTagged in H. destruct H.
  unfold FullTag. intros. unfold not. intros.
  assert ( Hl : checkV tc l /\ t l = None ). auto.
  apply H1 in Hl. apply length_zero_iff_nil in H0.
  rewrite H0 in Hl. simpl in Hl. apply Hl.
Qed.

Lemma bothinll : forall tc t ll l,
  GraphSat tc -> legal_tag tc t -> UnTagged tc t ll ->
  In l ll -> In (Reversebool l) ll.
Proof.
  intros. destruct H1. apply H3 in H2.
  destruct H2. pose proof ReverseNoneTag _ _ _ H0 H2 H4.
  pose proof Reverse_checkV tc l. apply H6 in H2.
  assert ( Hr : checkV tc (Reversebool l) /\ t (Reversebool l) = None ). auto. apply H3 in Hr. apply Hr.
Qed.

Lemma hdinll : forall tc t ll, 
  GraphSat tc -> legal_tag tc t -> 
  UnTagged tc t ll ->  0 < length ll -> 
  In (hd tb1 ll) ll /\ In (Reversebool (hd tb1 ll)) ll.
Proof.
  intros. split.
  + destruct ll.
    - simpl in H2. simpl. inversion H2.
    - simpl. left. reflexivity.
  + destruct ll.
    - simpl in H2. simpl. inversion H2.
    - simpl (hd tb1 (l :: ll)). assert ( Hin : In l (l :: ll) ).
      simpl. left. reflexivity.
      pose proof bothinll _ _ _ _ H H0 H1 Hin. apply H3.
Qed.

Lemma ExistUnTagged : forall tc t ll, 
  GraphSat tc -> legal_tag tc t -> 
  UnTagged tc t ll ->  0 < length ll -> 
  (exists x, In x ll /\ t x = None /\ ~ reachable (GraphGen tc) x (Reversebool x)).
Proof.
  intros. inversion H1. remember (hd tb1 ll) as top.
  pose proof hdinll _ _ _ H H0 H1 H2. destruct H5.
  rewrite <- Heqtop in H5. rewrite <- Heqtop in H6.
  unfold GraphSat in H. 
  pose proof H4 top. pose proof H4 (Reversebool top).
  apply H7 in H5 as H9. destruct H9.
  apply H8 in H6 as H11. destruct H11.
  pose proof H _ H9. apply not_and_or in H13.
  destruct H13.
  + exists top. auto.
  + exists (Reversebool top). rewrite Re_Re. auto.
Qed.

Check Classic.

Definition nt_tag (t : tag) (g : PreGraph lit (nat * bool)) (x y : lit) : option bool :=
  match t y with
  | Some true => Some true
  | Some false => Some false
  | None => match Classic (reachable g x y) with
            | left _ => Some true
            | right _ => match Classic (reachable g y (Reversebool x)) with
                       | left _ => Some false
                       | right _ => None
                       end
            end
  end.

Lemma Existstnext : forall tc t x, GraphSat tc ->
  legal_tag tc t -> checkV tc x -> t x = None -> 
  ~ reachable (GraphGen tc) x (Reversebool x) ->
  (exists tn, RProp tc t tn x).
Proof.
  intros. exists (nt_tag t (GraphGen tc) x).
  split.
  + intros. unfold nt_tag. destruct b'.
    - rewrite H4. reflexivity.
    - rewrite H4. reflexivity.
  + intros. split.
    - intros. unfold nt_tag. rewrite H4.
      destruct (Classic (reachable (GraphGen tc) x x')).
      reflexivity. congruence.
    - intros. unfold nt_tag in H5. rewrite H4 in H5.
      destruct (Classic (reachable (GraphGen tc) x x')). apply r.
      destruct (Classic (reachable (GraphGen tc) x' (Reversebool x))).
      congruence. congruence.
  + intros. split.
    - intros. unfold nt_tag. rewrite H4.
      destruct (Classic (reachable (GraphGen tc) x x')).
      pose proof reachable_trans _ _ _ _ r H5. congruence.
      destruct (Classic (reachable (GraphGen tc) x' (Reversebool x))).
      reflexivity. congruence.
    - intros. unfold nt_tag in H5. rewrite H4 in H5.
      destruct (Classic (reachable (GraphGen tc) x x')). congruence.
      destruct (Classic (reachable (GraphGen tc) x' (Reversebool x))). apply r. congruence.
  + intros. unfold nt_tag. rewrite H4.
    destruct (Classic (reachable (GraphGen tc) x x')).
    assert ( Some true <> None ) by congruence. tauto.
    destruct (Classic (reachable (GraphGen tc) x' (Reversebool x))).
    assert ( Some false <> None ) by congruence. tauto.
    tauto.
Qed.

Lemma Shortertn : forall tc t tn x ll, GraphSat tc ->
  legal_tag tc t -> checkV tc x -> t x = None -> 
  ~ reachable (GraphGen tc) x (Reversebool x) ->
  RProp tc t tn x -> UnTagged tc t ll -> 
  exists lln, UnTagged tc tn lln /\ length lln < length ll.
Proof.
  intros. pose proof RPropisLegal _ _ _ _ H H0 H1 H2 H3 H4.
  pose proof LegalTagllexists tc tn. destruct H7.
  exists x0. split. apply H7. inversion H7. inversion H5.
  assert ( incl x0 ll ). unfold incl. intros.
  rewrite H9 in H12. rewrite H11. destruct H12.
  split. apply H12. destruct (t a) eqn:HH.
  + pose proof RPr0 _ _ _ _ H4 _ _ HH. rewrite H13 in H14.
    congruence.
  + reflexivity.
  + pose proof NoDup_incl_length H8 H12.
    inversion H13.
    - assert ( ~ incl ll x0 ). unfold not. intros.
      unfold incl in H14. pose proof H14 x.
      pose proof H9 x. pose proof H11 x.
      rewrite H18 in H16. rewrite H17 in H16.
      pose proof H16 (conj H1 H2).
      assert ( reachable (GraphGen tc) x x ).
      rewrite reachable_ind_reachable.
      pose proof ind.reachable_nil (GraphGen tc) _ H1. apply H20.
      pose proof RPr1 _ _ _ _ H4 _ H2. rewrite H21 in H20.
      destruct H19. rewrite H22 in H20. congruence.
      assert ( length ll <= length x0 ). rewrite H15.
      apply le_n.
      pose proof NoDup_length_incl H8 H16 H12. congruence.
    - pose proof Lt.le_lt_n_Sm _ _ H15. apply H16.
Qed.

Lemma TagExist : forall tc, 
  GraphSat tc -> (exists t, Rtaggedgraph tc NullTag t).
Proof.
  intros. pose proof NullTagllexists tc as [ll ?].
  revert H0. pose proof NullisLegal tc. revert H0.
  generalize NullTag. remember (length ll) as n. revert ll Heqn.
  strong_induction n.
  intros. destruct n.
  + symmetry in Heqn. pose proof ZeroFullTag _ _ _ H1 Heqn.
    exists t. pose proof fully_tagged _ _ H2. apply H3.
  + pose proof PeanoNat.Nat.lt_0_succ n. rewrite Heqn in H2.
    pose proof ExistUnTagged _ _ _ H H0 H1 H2.
    destruct H3. destruct H3.
    pose proof proj2 H1 x. apply H5 in H3. 
    destruct H3. destruct H4.
    clear H4. pose proof Existstnext _ _ _ H H0 H3 H6 H7. 
    destruct H4 as [tn ?].
    pose proof Shortertn _ _ _ _ _ H H0 H3 H6 H7 H4 H1.
    destruct H8 as [lln ?]. destruct H8.
    remember (length lln) as nn. rewrite <- Heqn in H9.
    pose proof RPropisLegal _ _ _ _ H H0 H3 H6 H7 H4.
    pose proof IH nn H9 lln Heqnn _ H10 H8. 
    destruct H11 as [tl ?].
    assert ( Hx : checkV tc x /\ t x = None ).
    split. apply H3. apply H6.
    pose proof next_tag tc t tn tl x Hx H7 H4 H11.
    exists tl. apply H12.
Qed.

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

Definition tag_inj (t : tag) : injec :=
  fun n =>
  match t (n, true) with
  | Some b => b
  | None => false
  end.

Lemma allfalse : forall tc l1 l2 t, 
  GraphSat tc -> legal_tag tc t
  -> In (l1, l2) tc -> 
  ~ ( t l1 = Some false /\ t l2 = Some false).
Proof.
  intros. unfold not. intros.
  assert ( checkV tc l1 ). unfold checkV.
  exists (l1, l2). split. apply H1. simpl. left. auto.
  assert ( checkV tc l2 ). unfold checkV.
  exists (l1, l2). split. apply H1. simpl. right. auto.
  destruct H2.
  pose proof Pr0 _ _ H0 _ _ H3 H2. simpl in H6.
  pose proof Pr0 _ _ H0 _ _ H4 H5. simpl in H7.
  pose proof In_nth _ _ c1 H1. destruct H8. destruct H8.
  assert ( nthcl tc x = (l1, l2) ). unfold nthcl.
  apply H9. clear H9.
  assert ( checkE tc (x, true) ).
  unfold checkE. simpl. apply H8.
  assert ( st tc (x, true) = Reversebool l1 ).
  unfold st. simpl. rewrite H10. simpl. auto.
  assert ( ed tc (x, true) = l2 ).
  unfold ed. simpl. rewrite H10. simpl. auto.
  pose proof step_intro (GraphGen tc) _ _ _ H9 H11 H12.
  assert ( reachable (GraphGen tc) l2 l2 ).
  rewrite reachable_ind_reachable.
  apply ind.reachable_nil. apply H4.
  assert ( reachable (GraphGen tc) (Reversebool l1) l2 ).
  rewrite reachable_ind_reachable.
  assert ( (GraphGen tc) |= (Reversebool l1) ~> l2 ).
  split. apply Reverse_checkV. rewrite Re_Re. apply H3.
  split. apply H4. apply H13. 
  rewrite reachable_ind_reachable in H14.
  pose proof ind.reachable_cons (GraphGen tc) _ _ _ H15 H14.
  apply H16. apply Reverse_checkV in H3.
  pose proof Pr1 _ _ H0 _ _ H3 H4.
  unfold not in H16.
  assert (t (Reversebool l1) = Some true /\
      t l2 = Some false /\
      reachable (GraphGen tc) (Reversebool l1) l2).
  split. apply H6. split. apply H5. apply H15.
  apply H16 in H17. contradiction.
Qed.
  
Lemma full2inj : forall tc t, GraphSat tc -> FullTag tc t
  -> legal_tag tc t -> (exists inj, cnftrue inj tc).
Proof.
  intros. exists (tag_inj t). unfold cnftrue. unfold cleval.
  unfold liteval. intros. destruct c. destruct l. destruct l0.
  simpl. destruct b0.
  + destruct b2.
    - destruct (t (b, true)) eqn:HH.
      * destruct (t (b1, true)) eqn:HH1.
        { unfold tag_inj. rewrite HH. rewrite HH1.
          destruct b0, b2. auto. auto. auto.
          pose proof allfalse _ _ _ _ H H1 H2. destruct H3.
          split. apply HH. apply HH1. }
        { assert ( checkV tc (b1, true)).
          unfold checkV. simpl. exists (b, true, (b1, true)).
          split. apply H2. simpl. right. auto.
          pose proof H0 _ H3. congruence. }
      * assert ( checkV tc (b, true)).
        unfold checkV. simpl. exists (b, true, (b1, true)).
        split. apply H2. simpl. left. auto.
        pose proof H0 _ H3. congruence.
     - destruct (t (b, true)) eqn:HH.
      * destruct (t (b1, true)) eqn:HH1.
        { unfold tag_inj. rewrite HH. rewrite HH1.
          destruct b0, b2. auto. auto. unfold negb.
          assert ( checkV tc (b1, true)).
          unfold checkV. simpl. exists (b, true, (b1, false)).
          split. apply H2. simpl. right. auto.
          pose proof Pr0 _ _ H1 _ _ H3 HH1. simpl in H4.
          pose proof allfalse _ _ _ _ H H1 H2. destruct H5.
          split. apply HH. apply H4.
          unfold negb. auto. }
        { assert ( checkV tc (b1, true)).
          unfold checkV. simpl. exists (b, true, (b1, false)).
          split. apply H2. simpl. right. auto.
          pose proof H0 _ H3. congruence. }
      * assert ( checkV tc (b, true)).
        unfold checkV. simpl. exists (b, true, (b1, false)).
        split. apply H2. simpl. left. auto.
        pose proof H0 _ H3. congruence.
  + destruct b2.
    - destruct (t (b, true)) eqn:HH.
      * destruct (t (b1, true)) eqn:HH1.
        { unfold tag_inj. rewrite HH. rewrite HH1.
          destruct b0, b2. auto. unfold negb.
          assert ( checkV tc (b, true)).
          unfold checkV. simpl. exists (b, false, (b1, true)).
          split. apply H2. simpl. left. auto.
          pose proof Pr0 _ _ H1 _ _ H3 HH. simpl in H4.
          pose proof allfalse _ _ _ _ H H1 H2. destruct H5.
          split. apply H4. apply HH1. auto. auto. }
        { assert ( checkV tc (b1, true)).
          unfold checkV. simpl. exists (b, false, (b1, true)).
          split. apply H2. simpl. right. auto.
          pose proof H0 _ H3. congruence. }
      * assert ( checkV tc (b, true)).
        unfold checkV. simpl. exists (b, false, (b1, true)).
        split. apply H2. simpl. left. auto.
        pose proof H0 _ H3. congruence.
    - destruct (t (b, true)) eqn:HH.
      * destruct (t (b1, true)) eqn:HH1.
        { unfold tag_inj. rewrite HH. rewrite HH1.
          destruct b0, b2. unfold negb.
          assert ( checkV tc (b, true)).
          unfold checkV. simpl. exists (b, false, (b1, false)).
          split. apply H2. simpl. left. auto.
          assert ( checkV tc (b1, true)).
          unfold checkV. simpl. exists (b, false, (b1, false)).
          split. apply H2. simpl. right. auto.
          pose proof Pr0 _ _ H1 _ _ H3 HH. simpl in H5.
          pose proof Pr0 _ _ H1 _ _ H4 HH1. simpl in H6.
          pose proof allfalse _ _ _ _ H H1 H2. destruct H7.
          split. apply H5. apply H6.
          auto. auto. auto. }
        { assert ( checkV tc (b1, true)).
          unfold checkV. simpl. exists (b, false, (b1, false)).
          split. apply H2. simpl. right. auto.
          pose proof H0 _ H3. congruence. }
      * assert ( checkV tc (b, true)).
        unfold checkV. simpl. exists (b, false, (b1, false)).
        split. apply H2. simpl. left. auto.
        pose proof H0 _ H3. congruence.
Qed.

Definition TsatToScc: forall tc,(exists inj, cnftrue inj tc) <-> GraphSat tc.
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
        { pose proof Reverse_checkV tc l. apply H3. apply H0. }
        { apply H0. }
      * left. unfold "~". intros. apply reach_eq_nece in H2.
        unfold necessary in H2. specialize (H2 x).
        apply H2 in H.
        { rewrite H in H1. apply H1. reflexivity. }
        { apply H0. } { pose proof Reverse_checkV tc l. apply H3. apply H0. }
        { apply not_true_is_false in H1. 
          rewrite <- neg_Reverselit in H1. apply negb_false_iff.
          rewrite H1. reflexivity. } { apply H0. }
        { pose proof Reverse_checkV tc l. apply H3. apply H0. }
  + intros. pose proof GraphSattotag NullTag _ H. pose proof lttoFull. pose proof TagExist _ H. destruct H2.
    pose proof H1 _ _ H H2.
    pose proof GraphSattotag _ _ H H2.
    pose proof full2inj _ _ H H3 H4.
    apply H5.
Qed.