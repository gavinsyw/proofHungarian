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

Section Matching.
(*以下都是对于图 BG 而言*)
Context {BG: BiGraph}.

(**下面是关于  匹配 的定义 *)
Definition matching := list E. 
(**
里面的边不相交
每一对匹配点之间都连接了两条有向边
*)

Definition is_matching (m: list E): Prop :=
disjoint_edges_set BG m /\ forall e, In e m -> In (eo BG e) m /\ In e (Elist BG).

Fixpoint Ma (v : V) (M :matching): (option V) := 
match M with 
|nil => None (**该点为非匹配点*)
|e::m' => if Nat.eqb (src BG e) v then 
          Some (dst BG e) else 
            (Ma v m')
end.

(**定义了一个通用的matching*)
Context {M : matching}.
Hypothesis base_Match_re : is_matching M.

Definition Matching (v: V) : (option V) := Ma v M. (*对于一个点找到M中它的匹配点*)



(*  下面给出图的点集 边集和 某个点的连接点集 *)


Inductive step  : V -> V -> Prop :=
|step_intro : forall e  x y ,
                 evalid BG e ->
                 src BG e = x ->
                 dst BG e = y -> step  x y.


Definition connected (v: V) (cl : list V) : Prop :=
  forall (x : V ),  step  v x <-> In x cl.

Definition  LV:= Vlist BG.
Definition LE:=Elist BG.

Definition get_connectednode_func  := V -> list V.

Definition con : V -> list V := con_pre LE.

Hypothesis conlistre : forall v , connected v (con v).


Definition Max := length(LV).


(* 找到对于一个Vstateb中从大到小的第一个没有被访问过的*)

Fixpoint conn (v: V) (v1 : Vstateb) (n:nat): V :=
match n with
|O => O
|S n' =>  if Inb (S n') (con v) then 
             (if v1 (S n') then n else conn v v1 n')
             else conn v v1 n'
end.

Definition max_conn (v : V) (v1 : Vstateb) := conn v v1 Max.


(*路径的定义*)
Definition e_to_v (p : list E) : list V := e_to_vth BG p .


Definition path : Type := (V * list E)%type.

Variable de : E. (*边的default值*)

(**定义
  交错路 : 一条匹配边一条非匹配边
  增广路 ：由非匹配边开始，交错路，以非匹配边结束*)
Fixpoint cross_path (l: list E) : Prop :=
match l with
|nil => True
|m::nil => True
|m::l' => (* actually hd de l' 不会用到default值*)
             ( In m M /\ ~ In (hd de l') M  \/ 
                   ~ In m M /\  In (hd de l') M)
             /\ cross_path l'
end.

(*保证最后一条边为非匹配边的交错路*)
Fixpoint aug_path_pre (l: list E) : Prop :=
match l with 
|nil => False
|m::nil => ~ In m M
|m::n::l' => (~ In m M /\ In n M )/\ 
          (cross_path l' /\ cross_path (n::l')) 
end.
(* 增广路径 *)
Definition  aug_path (l : list E) : Prop :=  
        aug_path_pre l /\ (1<= length l /\ ~ In (last l de) M) 
            /\ Matching (snd (hd de l)) =None /\  Matching (fst (last l de)) =None. 


(**小步语义*)
Inductive cross_step : (Vstateb * path) -> (Vstateb * path ) -> Prop := 
| one_v : forall (u w: V ) (e1 e2 : E) (v1 : Vstateb) ,
    Matching u  = None -> let v := max_conn u v1  in 
    src BG e1 = u -> dst BG e1 = v  ->src BG e2 = v -> dst BG e2 = w ->~ In e1 M ->  In e2 M -> 
    (*-> Matching v = Some w -> *)
         cross_step (Vstateb_update default_Vstateb u, (u, nil)) ( Vstateb_update (Vstateb_update (Vstateb_update default_Vstateb u)  v) w  , (w ,e2 :: (e1::nil))) 
(**从一个非匹配点 经过非匹配边和匹配边  到一个匹配点 *)
| not_one : forall (u  w: V ) (e1 e2 e3 : E)(p :list E) (v1: Vstateb), (* ???  *) 
    dst BG e3 = u -> In e3 M -> let v := max_conn u v1 in
    (* Nat.odd (length p) = true ->*)
    v1 u = true -> v1 w = false  ->
    src BG e1 = u -> dst BG e1 = v  -> src BG e2 = v -> dst BG e2 = w -> In e2 M -> ~ In e1 M
    ->(*->
      Matching v = Some w -> *)
         cross_step (v1, (u, e3 :: p)) ( Vstateb_update (Vstateb_update v1  v) w  , (w ,e2::(e1::(e3::p))))
(**从一个匹配点 经过非匹配边和匹配边  到一个匹配点 *)
|yes_to_no : forall (u v : V ) (e1 e2 : E) (p: list E)  (v1 : Vstateb) ,
   dst BG e2 = u ->  In e2 M -> v1 u = true -> let v := max_conn u v1 in
   Matching v = None ->
   src BG e1 = u -> dst BG e1 = v  -> ~ In e1 M ->
         cross_step (v1, (u, e2::p)) ( Vstateb_update v1  v , (v ,e1::(e2::p)))
(**从一个匹配点到非匹配点*)
|no_to_no :  forall (u : V ) (e1 :E)  ,
    Matching u  = None -> let v := max_conn u  (Vstateb_update default_Vstateb u) in 
    Matching v = None ->
    src BG e1 = u -> dst BG e1 = v  -> ~ In e1 M ->
         cross_step (Vstateb_update default_Vstateb u, (u, nil)) 
         (Vstateb_update (Vstateb_update default_Vstateb u) v,(v, e1 :: nil) )
(* *)
|Back_to_yes : forall (u w1 w2: V ) (e1 e2 e3: E)(p :list E) 
               (v1: Vstateb),
      dst BG e3 = w2 -> In e3 M ->
      v1 u = true -> max_conn u v1 = O -> 
            In e1 M ->  ~In e2 M -> 
              src BG e1 = w1 -> dst BG e1 = u  -> src BG e2 = w2 -> dst BG e2 = w1 ->
           cross_step (v1, (u, e1::(e2::(e3::p)))) ( Vstateb_update_fl v1 (list_sub (con u) (e_to_v p) ) , (w2 ,e3::p))
(**回溯到上一个匹配点*) 
|Back_to_no : forall (u w1 w2 : V) (e1 e2 : E) (p : list E )
              (v1 : Vstateb) ,
     v1 u = true -> max_conn u v1 = O -> 
           In e1 M ->  ~In e2 M -> 
             src BG e1 = w1 -> dst BG e1 = u  -> src BG e2 = w2 -> dst BG e2 = w1 ->
           cross_step (v1, (u, e1::(e2::nil))) ( Vstateb_update_fl v1 (list_sub (con u )(e_to_v p) ) , (w2 ,nil))
(** 回溯到初始状态即一个点*)    .



Inductive cross_halt : (Vstateb * path) -> Prop :=
|success : forall (u : V) (v : Vstateb) (e : E )(p : list E),
              Matching u = None ->
            v u = true -> dst BG e = u -> ~ In e M -> cross_halt (v , (u, e::p)).
Definition state := (Vstateb * path)%type.
Definition multi_cstep : state -> state -> Prop := clos_refl_trans cross_step .





(**下面是定理*)
(*
首先证明小步成功停止得到路径path的长度为奇数 Theorem path_odevity
接着证明交错路经过多步到达下一个状态得到的path仍然是交错路 Theorem cross_stay
再证明小步由一个非匹配点出发成功停止的path第一条边为非匹配边即不在M里面 Theorem cross_start
最后证明由一个点出发，成功停止的path为增广路

后面证明增广路得到更大的匹配
*)

Lemma half_halt :
  forall st1 st2, cross_step st1 st2 -> ~ cross_halt st1.
Proof.
  intros.
  unfold not; intros; inversion H.
  - rewrite <- H8 in H0.
    inversion H0.
  - rewrite <- H11 in H0.
    inversion H0. subst. auto.
  - rewrite <- H8 in H0.
    inversion H0. subst. auto.
  - rewrite <- H6 in H0.
    inversion H0.
  - rewrite <- H11 in H0.
    inversion H0. subst. auto.
  - rewrite <- H9 in H0.
    inversion H0. subst. auto.
Qed.

Lemma stay_even :
  forall st1 st2, cross_step st1 st2 -> ~cross_halt st2 -> 
    Nat.even (length (snd (snd st1))) = Nat.even (length (snd (snd st2))).
Proof.
  intros.
  induction H.
  - simpl. reflexivity.
  - unfold snd. reflexivity.
  - unfold not in H0. destruct H0. apply success.
    auto.  unfold Vstateb_update. 
    assert (Nat.eqb v0 v0 = true). 
    apply PeanoNat.Nat.eqb_refl.
    rewrite H0. reflexivity.
    auto. auto.
  - unfold not in H0. destruct H0. apply success.
    auto. unfold Vstateb_update at 1.
    assert (Nat.eqb v v = true). 
    apply PeanoNat.Nat.eqb_refl.
    rewrite H0. reflexivity.
    auto. auto.
  - unfold snd. reflexivity.
  - unfold snd. reflexivity.
Qed.

Theorem try :
  forall  ( v: V) st , ~ cross_halt st ->
    multi_cstep ( Vstateb_update default_Vstateb v, (v, nil)) st -> 
      Nat.even (length (snd (snd st))) = true.
Proof.
  intros.
  apply Operators_Properties.clos_rt_rtn1_iff in H0.
  induction H0.
  - reflexivity.
  - pose proof (half_halt y z H0) .
    pose proof (IHclos_refl_trans_n1 H2).
    rewrite <- H3.
    apply eq_sym.
    apply stay_even; auto.
Qed.

Lemma cons_length : forall (v: E) l , length (v::l) = S (length l).
Proof.
  intros.
  induction l.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
Lemma S_even : forall n , Nat.even (S n) = negb (Nat.even n).
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - rewrite IHn. simpl. rewrite Bool.negb_involutive. reflexivity.
Qed.
Lemma list_ode: forall (v: E) l,  Nat.even (length l) =Nat.odd (length ( v:: l)).
Proof.
 intros. revert v.
 induction l.
 - simpl. reflexivity.
 - unfold Nat.odd. rewrite cons_length. intros. rewrite cons_length. 
   rewrite S_even. rewrite S_even. rewrite Bool.negb_involutive.
   unfold Nat.odd in IHl. rewrite (IHl a). apply Bool.negb_involutive.
Qed.


Lemma notmatching : forall v e M, src BG e = v -> 
     In e M -> ~ Ma v M = None .
Proof.
  intros.
  unfold not.
  intros. induction M0.
  - inversion H0.
  - inversion H0. rewrite H2 in H1. rewrite <- H in H1. simpl in H1.
    rewrite PeanoNat.Nat.eqb_refl in H1. inversion H1.
    simpl in H1. destruct (Nat.eqb (src BG a) v). inversion H1. apply IHM0. auto. auto.
Qed.

Lemma notmatching_rev : forall v e M, src BG e = v -> 
      Ma v M = None -> ~ In e M .
Proof.
  intros.
  unfold not.
  intros. induction M0.
  - inversion H1.
  - inversion H1. rewrite H2 in H0. rewrite <- H in H0. simpl in H0.
    rewrite PeanoNat.Nat.eqb_refl in H0. inversion H0.
    simpl in H0. destruct (Nat.eqb (src BG a) v). inversion H0. apply IHM0. auto. auto.
Qed.

Lemma change_even :
  forall st1 st2, cross_step st1 st2 -> cross_halt st2 -> 
    Nat.even (length (snd (snd st1))) = Nat.odd (length (snd (snd st2))).
Proof.
  intros.
  induction H.
  - inversion H0. unfold not in H14. apply H14 in H6.  inversion H6.
  - inversion H0. unfold not in H17. apply H17 in H8.  inversion H8.
  - unfold snd . pose proof (list_ode e1 (e2 :: p)). apply H7.
  - unfold snd. apply list_ode.
  - inversion H0. unfold not in H17. apply H17 in H1.  inversion H1.
  - inversion H0.
Qed.


Theorem path_odevity :
 forall v st, cross_halt st -> 
      multi_cstep ( Vstateb_update default_Vstateb v, (v, nil)) st -> 
      Nat.odd (length (snd (snd st))) = true.
Proof.
 intros.
 apply Operators_Properties.clos_rt_rtn1_iff in H0.
 induction H0.
 - inversion H.
 - pose proof (half_halt y z H0).
   assert ( multi_cstep ( Vstateb_update default_Vstateb v, (v, nil)) y).
   unfold multi_cstep. apply Operators_Properties.clos_rt_rtn1_iff. apply H1.
   pose proof (try v y H2 H3).
   pose proof (change_even y z H0 H). rewrite H5 in H4. auto.
Qed.




Lemma cross_stay_unit : forall y z ,
   cross_step y z -> 
       cross_path (snd (snd y)) -> cross_path (snd (snd z)).
Proof.
  intros.
  induction H.
  - simpl. split. 2: auto.  left. split. auto. 
    pose proof ( notmatching_rev u e1 M). apply H7. auto. auto.
  - split. auto. unfold snd in H0. split. auto. auto.
  - unfold snd. unfold snd in H0. split. auto. auto.
  - unfold snd. unfold snd in H0. reflexivity.
  - unfold snd. unfold snd in H0. destruct H0. destruct H10. auto.
  - unfold snd. reflexivity.
Qed.


Theorem cross_stay :
  forall st1 st2, cross_path (snd (snd st1)) ->
      multi_cstep  st1  st2 -> 
      cross_path (snd (snd st2)).
Proof.
 intros.
 apply Operators_Properties.clos_rt_rtn1_iff in H0.
 induction H0.
 - unfold snd. auto. 
 - pose proof ( cross_stay_unit y z  H0 IHclos_refl_trans_n1 ). auto.
Qed.

Lemma cross_start_simpl :
 forall  v st,
    multi_cstep ( Vstateb_update default_Vstateb v, (v, nil)) st ->
    cross_path (snd (snd st)).
Proof.
  intros.
  assert (cross_path (snd (snd 
            (Vstateb_update default_Vstateb v, (v, nil))))).
  unfold snd. reflexivity.
  eapply cross_stay. apply H0. auto.
Qed.


Lemma  first_match: forall v y , 
     cross_step (Vstateb_update default_Vstateb v, (v, nil)) y ->
       ~ In (last (snd (snd y)) de) M.
Proof.
  intros.
  inversion H.
  - unfold snd. unfold last. auto.
  - unfold snd. unfold last. auto.
Qed.

Lemma  path_stay_unit: forall x y,
      ~ (snd (snd x)) = nil -> ~ (snd (snd y)) = nil ->
       cross_step x y -> ~ In (last (snd (snd x)) de) M -> 
               ~ In (last (snd (snd y)) de) M.
Proof.
  intros.
  unfold not. intros.
  inversion H1.
  - subst. unfold snd in H. unfold not in H. apply H. auto.
  - subst. unfold snd in H0. unfold snd in H3. unfold snd in H2.
    simpl in H3. simpl in H2. unfold not in H2. apply H2. apply H3.
  - subst. unfold snd in H0. unfold snd in H3. unfold snd in H2.
    unfold not in H2. apply H2. simpl in H3. simpl. apply H3.
  - subst. unfold snd in H. unfold not in H. apply H. auto.
  - subst.  unfold snd in H0. unfold snd in H3. unfold snd in H2.
    unfold not in H2. apply H2. simpl in H3. simpl. apply H3.
  -  subst. unfold snd in H0. unfold not in H0. apply H0. auto.
Qed.

Theorem path_stay : forall x y,
    ~ (snd (snd x)) = nil -> ~ (snd (snd y)) = nil ->
       multi_cstep x y -> ~ In (last (snd (snd x)) de) M -> 
               ~ In (last (snd (snd y)) de) M.
Proof.
  intros.
  apply Operators_Properties.clos_rt_rtn1_iff in H1.
  induction H1.
  - auto.
  - inversion H1.
    eapply first_match. rewrite <- H11 in H1. rewrite H12.  apply H1.
    eapply path_stay_unit. 3: rewrite H15; apply H1.  rewrite <- H14.
    simpl. unfold not. intros. inversion H16. unfold snd. 
    unfold not. intros. inversion H16. rewrite <- H14. unfold snd.
    rewrite <- H14 in IHclos_refl_trans_n1. 
    unfold snd in IHclos_refl_trans_n1. apply IHclos_refl_trans_n1.
    unfold not. intros. inversion H16.
    unfold snd. rewrite <- H11 in IHclos_refl_trans_n1.
    unfold snd in IHclos_refl_trans_n1.
    unfold last. unfold last in IHclos_refl_trans_n1.
    apply IHclos_refl_trans_n1. unfold not. intros. inversion H13.
    unfold snd. unfold last. auto.
    unfold snd. rewrite <- H14 in IHclos_refl_trans_n1.
    unfold snd in IHclos_refl_trans_n1.
    unfold last. unfold last in IHclos_refl_trans_n1.
    apply IHclos_refl_trans_n1. unfold not. intros. inversion H16.
    rewrite <- H13 in H0. unfold not in H0. unfold not. intros.
    apply H0. auto.
Qed.

Lemma cross_start_pre:
  forall v st, ~ (snd (snd st)) = nil ->
     multi_cstep ( Vstateb_update default_Vstateb v, (v, nil)) st ->
       ~ In (last (snd (snd st)) de) M.
Proof.
  intros.
  apply Operators_Properties.clos_rt_rt1n_iff in H0.
  inversion H0.
  - subst.  unfold snd in H. unfold not in  H. auto. 
  - pose proof (path_stay y z).
    subst.
    apply H4.
      inversion H1. unfold snd. unfold not.  intros.
    inversion H14. unfold snd. unfold not.  intros.
    inversion H12.
      auto.
      apply Operators_Properties.clos_rt_rt1n_iff . auto.
      eapply first_match. apply H1.
Qed.


Theorem cross_start:
  forall v st, cross_halt st ->
     multi_cstep ( Vstateb_update default_Vstateb v, (v, nil)) st ->
       ~ In (last (snd (snd st)) de) M.
Proof.
  intros.
  eapply cross_start_pre.
  2: apply H0.
  inversion H. unfold snd. unfold not. intros. inversion H6.
Qed.

Lemma path_first_decide : forall p,
  cross_path p -> ~ In (last p de) M -> 1 <= length p ->
    ( Nat.odd (length p)=true  /\   ~ In (hd de p) M ) \/ 
      (Nat.odd (length p) = false /\  In (hd de p) M).
Proof.
  intros.
  induction p.
  - inversion H1.
  - destruct p.
    + left. simpl in H0. simpl. auto.
    + simpl. destruct H. unfold last in IHp. unfold last in H0.
      pose proof (IHp H2 H0 ). simpl in H3. assert( 1<= S(length p)).
      omega. apply H3 in H4. unfold hd in H. destruct H4.
        destruct H4. right. split. unfold Nat.odd. rewrite S_even.
        rewrite Bool.negb_involutive. unfold Nat.odd in H4.
        rewrite Bool.negb_true_iff in H4. auto.
        destruct H. destruct H. auto. destruct H. unfold not in H5.
        apply H5 in H6. inversion H6.
        destruct H4.
        left. split. unfold Nat.odd. rewrite S_even.
        rewrite Bool.negb_involutive. unfold Nat.odd in H4.
        rewrite Bool.negb_false_iff in H4. auto.
        destruct H. destruct H. unfold not in H6.
        apply H6 in H5. inversion H5. destruct H.
        auto.
Qed.


Lemma st_ed_unmatched:
  forall (p: list E) (v: V) st, aug_path_pre p -> cross_halt st -> multi_cstep (Vstateb_update default_Vstateb v, (v, nil)) st -> Matching (fst (snd st)) = None.
Proof.
  intros.
  apply Operators_Properties.clos_rt_rtn1_iff in H1.
  induction H1.
  inversion H0.
  inversion H0.
  unfold snd.
  unfold fst.
  exact H3.
Qed.


Lemma path_to_aug : forall p ,
    cross_path p ->  ~ In (last p de) M -> 
      Nat.odd (length p) = true  ->
          aug_path_pre p.
Proof.
 intros.
 induction p.
 - inversion H1.
 - destruct p.
   simpl. simpl in H1. auto. assert (1<= length((a :: e :: p))).
   simpl. omega. assert (1<= length (e::p)). simpl. omega.
   pose proof (path_first_decide (a::e::p) H H0 H2). destruct H.
   assert ( ~ In (last (e::p) de) M). unfold last. unfold last in H0.
   auto.
   pose proof (path_first_decide (e::p) H5 H6 H3).
   split.
   destruct H4. destruct H4. unfold hd in H8. split. auto.
     destruct H7. destruct H7. unfold Nat.odd in H7.
     unfold Nat.odd in H4. simpl in H4. rewrite Bool.negb_true_iff in H4.
     rewrite Bool.negb_true_iff in H7. assert (length(e::p) = S(length p)).
     reflexivity. rewrite H10 in H7. rewrite S_even in H7.
     rewrite Bool.negb_false_iff in H7. rewrite H4 in H7. inversion H7.
     destruct H7. unfold hd in H9. auto.
     destruct H4. rewrite H4 in H1. inversion H1.
   split. 2: auto.
   destruct p.
   + reflexivity.
   + destruct H5. auto.
Qed.


(**终极定理： 小步得到的确实是 增广路径！*)
Lemma step_to_aug_pre: forall v st, cross_halt st ->
     multi_cstep ( Vstateb_update default_Vstateb v, (v, nil)) st ->
       aug_path_pre (snd (snd st)) .
Proof.
  intros.
  eapply (path_to_aug (snd (snd st))).
  eapply cross_stay. 2: apply H0. reflexivity.
  eapply cross_start. auto. apply H0.
  eapply path_odevity. auto. apply H0.
Qed.








Lemma  first_match_node: forall v y , 
     cross_step (Vstateb_update default_Vstateb v, (v, nil)) y ->
       Matching (fst (last (snd (snd y)) de))  =None.
Proof.
  intros.
  inversion H.
  - unfold snd. unfold last. unfold src in H3. subst. auto.
  - unfold snd. unfold last. unfold src in H4. subst.  auto.
Qed.

Lemma  path_stay_unit_node: forall x y,
      ~ (snd (snd x)) = nil -> ~ (snd (snd y)) = nil ->
       cross_step x y -> Matching (fst (last (snd (snd x)) de))  =None ->
          Matching (fst (last (snd (snd y)) de))  = None.
Proof.
  intros.
  unfold not. intros.
  inversion H1.
  - subst. unfold snd in H. unfold not in H.  auto.
  - subst. unfold snd in H2. unfold last in H2. unfold snd. unfold last. auto.
  - subst. unfold snd in H2. unfold last in H2. unfold snd. unfold last. auto.
  - subst. unfold snd in H. unfold not in H.  auto.
  - subst.  unfold snd in H2. unfold last in H2. unfold snd. unfold last. auto.
  -  subst. unfold snd in H0. unfold not in H0.
     assert (False). apply H0.   auto. inversion H7.
Qed.

Theorem path_stay_node : forall x y,
    ~ (snd (snd x)) = nil -> ~ (snd (snd y)) = nil ->
       multi_cstep x y -> Matching (fst (last (snd (snd x)) de))  =None ->
          Matching (fst (last (snd (snd y)) de))  = None.
Proof.
  intros.
  apply Operators_Properties.clos_rt_rtn1_iff in H1.
  induction H1.
  - auto.
  - inversion H1.
    eapply first_match_node. rewrite <- H11 in H1. rewrite H12.  apply H1.
    eapply path_stay_unit_node. 3: rewrite H15; apply H1.  rewrite <- H14.
    simpl. unfold not. intros. inversion H16. unfold snd. 
    unfold not. intros. inversion H16. rewrite <- H14. unfold snd.
    rewrite <- H14 in IHclos_refl_trans_n1. 
    unfold snd in IHclos_refl_trans_n1. apply IHclos_refl_trans_n1.
    unfold not. intros. inversion H16.
    unfold snd. rewrite <- H11 in IHclos_refl_trans_n1.
    unfold snd in IHclos_refl_trans_n1.
    unfold last. unfold last in IHclos_refl_trans_n1.
    apply IHclos_refl_trans_n1. unfold not. intros. inversion H13.
    unfold snd. unfold last. auto.
    unfold snd. rewrite <- H9 in IHclos_refl_trans_n1.
    unfold snd in IHclos_refl_trans_n1.
    unfold last. unfold last in IHclos_refl_trans_n1. unfold src in H6. subst. auto.
    unfold snd.
    rewrite <- H14 in IHclos_refl_trans_n1. unfold snd in IHclos_refl_trans_n1.
    assert (e1 :: e2 :: e3 :: p <>nil). unfold not. intros. inversion H16.
    apply IHclos_refl_trans_n1 in H16. unfold last in H16 . unfold last. auto.
    rewrite <- H13 in H0. unfold snd in H0. unfold not in H0.
     assert (False). apply H0.   auto. inversion H14. 
Qed.

Lemma cross_start_node_pre:
  forall v st, ~ (snd (snd st)) = nil ->
     multi_cstep ( Vstateb_update default_Vstateb v, (v, nil)) st ->
       Matching (fst (last (snd (snd st)) de))  = None.
Proof.
  intros.
  apply Operators_Properties.clos_rt_rt1n_iff in H0.
  inversion H0.
  - subst.  unfold snd in H. unfold not in  H. assert (False).
    apply H.   auto. inversion H1.
  - pose proof (path_stay_node y z).
    subst.
    apply H4.
      inversion H1. unfold snd. unfold not.  intros.
    inversion H14. unfold snd. unfold not.  intros.
    inversion H12.
      auto.
      apply Operators_Properties.clos_rt_rt1n_iff . auto.
      eapply first_match_node. apply H1.
Qed.


Theorem cross_start_node:
  forall v st, cross_halt st ->
     multi_cstep ( Vstateb_update default_Vstateb v, (v, nil)) st ->
        Matching (fst (last (snd (snd st)) de))  = None.
Proof.
  intros.
  eapply cross_start_node_pre.
  2: apply H0.
  inversion H. unfold snd. unfold not. intros. inversion H6.
Qed.


Theorem step_to_aug: forall v st, cross_halt st ->
     multi_cstep ( Vstateb_update default_Vstateb v, (v, nil)) st ->
       aug_path (snd (snd st)) .
Proof.
  intros.
  unfold aug_path. pose proof (cross_start_node v st H H0).
  split.
  apply (step_to_aug_pre v). auto. auto.
  split. split. inversion H. simpl. omega.
  apply (cross_start_pre v).
  3:split. 4:auto.
  inversion H. simpl. unfold not. intros. inversion H7. auto.
  inversion H. simpl. unfold dst in H4. subst. auto.
Qed.
(**下面证明增广路得到更大的匹配*)


(**下面证明增广路得到更大的匹配*)

Definition xor_edge (e1 p: list E) : list E :=
  list_sub_e e1 p ++ list_sub_e p e1.

Lemma list_sub_left_notIn_stay : forall a p m, ~In a m ->
  list_sub_e (a::p) m = a::list_sub_e p m.
Proof.
  intros.
  revert p; induction m.
  tauto.
  pose proof classic (E_eqb a0 a = true).
  destruct H0.
  unfold not in H.
  destruct H.
  - unfold In.
    left.
    rewrite -> E_eqb_eq  in H0.
    exact H0.
  - apply Bool.not_true_is_false in H0.
    simpl.
    rewrite H0.
    assert (~In a m).
    unfold not.
    unfold not in H.
    intros. apply H.
    simpl.
    right. exact H1.
    intros.
    pose proof (IHm H1).
    specialize (H2 (remove_e a0 p)).
    exact H2.
Qed.

Theorem list_sub_left_notIn : forall a p m, ~ In a m  -> 
    length (list_sub_e (a::p) m)  =S (length (list_sub_e p m)).
Proof.
  intros.
  pose proof (list_sub_left_notIn_stay a p m).
  pose proof (H0 H).
  rewrite H1.
  reflexivity.
Qed.

Lemma list_remove_notIn : forall a m, ~In a m -> 
    remove_e a m = m.
Proof.
  induction m; intros.
  auto.
  simpl.
  simpl in H.
  apply not_or_and in H.
  Search (E_eqb).
  destruct H.
  apply not_eq_sym in H.
  rewrite <- E_eqb_eq in H.
  apply Bool.not_true_is_false in H.
  rewrite H.
  apply IHm in H0.
  rewrite H0.
  auto.
Qed.

Lemma list_sub_right_notIn_stay : forall a p m, ~In a m ->
    list_sub_e m (a::p) = list_sub_e m p.
Proof.
  intros.
  simpl.
  pose proof (list_remove_notIn a m H).
  rewrite H0.
  auto.
Qed.

Theorem list_sub_right_notIn : forall a p m, ~In a m -> 
    length (list_sub_e m (a::p)) = length (list_sub_e m p).
Proof.
  intros.
  pose proof (list_sub_right_notIn_stay a p m H).
  rewrite H0.
  auto.
Qed.

Theorem even_cons : forall {A: Type} (a:A) p , 
            Nat.even (length (a::p ))  = negb (Nat.even (length p)).
Proof.
  intros.
  rewrite <- S_even.
  assert (length (a::p) = S (length p)).
  reflexivity.
  rewrite H.
  tauto.
Qed.

Theorem list_sub_length_cons_notIn: forall a p m ,
         ~ In a m ->  
         length (list_sub_e m p) + length (list_sub_e  p m) <
           length (list_sub_e m (a :: p)) + length (list_sub_e (a :: p) m).
Proof.
  intros.
  pose proof (list_sub_left_notIn a p m H).
  pose proof (list_sub_right_notIn a p m H).
  rewrite H0.
  rewrite H1.
  omega.
Qed.

Lemma In_notIn_neq : forall a a0 m,
    In a m -> ~In a0 m -> E_eqb a a0 = false.
Proof.
  induction m; intros.
  simpl in H.
  destruct H.
  simpl in H.
  simpl in H0.
  apply not_or_and in H0.
  destruct H0; destruct H.
  rewrite H in H0.
  rewrite <- E_eqb_eq in H0.
  apply Bool.not_true_is_false in H0.
  exact H0.
  pose proof (IHm H H1).
  exact H2.
Qed.

Lemma In_notIn_neq_refl : forall a a0 m,
    In a m -> ~In a0 m -> E_eqb a0 a = false.
Proof.
  induction m; intros.
  simpl in H.
  destruct H.
  simpl in H.
  simpl in H0.
  apply not_or_and in H0.
  destruct H0; destruct H.
  rewrite H in H0.
  apply not_eq_sym in H0.
  rewrite <- E_eqb_eq in H0.
  apply Bool.not_true_is_false in H0.
  exact H0.
  pose proof (IHm H H1).
  exact H2.
Qed.

Lemma list_sub_right_In_stay : forall a a0 p m,
    In a m -> ~In a0 m -> ~In a p ->
    length (list_sub_e (a0 :: m) p) = S (length (list_sub_e (a0 :: remove_e a m) p)).
Proof.
  intros.
  pose proof classic (In a0 p).
Admitted.

Theorem list_sub_right_In : forall a p m,
    In a m -> ~In a p -> NoDup m -> length(list_sub_e m p) = S (length (list_sub_e m (a::p))).
Proof.
  intros.
  revert H0; revert p; induction m; intros.
  inversion H.
  destruct H.
  - simpl.
    simpl in H.
    rewrite <- H in H0, IHm.
    rewrite <- H.
    apply eq_sym in H.
    rewrite E_eqb_relf.
    pose proof (list_sub_left_notIn a0 m p H0).
    pose proof (NoDup_Add).
    specialize (H3 E a0 m (a0::m)).
    assert (Add a0 m (a0::m)).
    apply Add_head.
    apply H3 in H4.
    rewrite -> H4 in H1.
    destruct H1.
    pose proof (list_remove_notIn a0 m H5).
    rewrite H6.
    pose proof (list_sub_left_notIn a0 m p H0).
    exact H7.
  - pose proof (NoDup_Add).
    specialize (H2 E a0 m (a0::m)).
    assert (Add a0 m (a0::m)).
    apply Add_head.
    apply H2 in H3.
    rewrite -> H3 in H1.
    destruct H1.
    pose proof (IHm H H1).
    pose proof (In_notIn_neq a a0 m H H4).
    specialize (H5 p).
    simpl.
    rewrite H6.
    clear IHm H2 H3 H6 H1.
    pose proof (list_sub_right_In_stay a a0 p m H H4 H0).
    exact H1.
Qed.

Lemma remove_e_not_in : forall a a0 p, ~In a p -> ~In a (remove_e a0 p).
Proof.
  unfold not; intros.
  destruct H.
  induction p.
  auto.
  pose proof classic (a= a1).
  destruct H.
  unfold In.
  left. auto.
  assert (In a p).
  admit.
  unfold In.
  right.
  exact H1.
Admitted.

Lemma list_sub_left_In_stay : forall a p m, In a m -> ~In a p -> NoDup m ->
    list_sub_e p m = list_sub_e (a::p) m.
Proof.
  intros.
  revert H0; revert p; induction m; intros.
  destruct H.
  simpl in H. destruct H.
  simpl.
  rewrite <- E_eqb_eq in H.
  rewrite H.
  tauto.
  pose proof (NoDup_Add).
  specialize (H2 E a0 m (a0::m)).
  assert (Add a0 m (a0::m)).
  apply Add_head.
  apply H2 in H3.
  rewrite H3 in H1.
  destruct H1.
  pose proof (IHm H H1).
  simpl.
  pose proof (In_notIn_neq_refl a a0 m H H4).
  rewrite H6.
  specialize (H5 (remove_e a0 p)).
  assert (~In a (remove_e a0 p)).
  apply remove_e_not_in.
  exact H0.
  apply H5 in H7.
  exact H7.
Qed.

Theorem list_sub_left_In : forall a p m, In a m -> ~In a p -> NoDup m ->
    length (list_sub_e p m) = length (list_sub_e (a::p) m).
Proof.
  intros.
  pose proof (list_sub_left_In_stay a p m H H0 H1).
  rewrite H2.
  auto.
Qed.

Theorem list_sub_length_cons_In: forall a p m ,
          In a m -> ~In a p -> NoDup m ->
         length (list_sub_e m p) + length (list_sub_e  p m) = S 
           ( length (list_sub_e m (a :: p)) + length (list_sub_e (a :: p) m)).
Proof.
  intros.
  pose proof (list_sub_left_In a p m H H0 H1).
  pose proof (list_sub_right_In a p m H H0 H1).
  rewrite H2.
  rewrite H3.
  auto.
Qed.

Theorem NotSmall : forall p , 
 cross_path p -> 1 <=length (p) -> ~ In (last p de) M ->
   ( Nat.even (length p) =true /\ length M   <= length (xor_edge M p)) 
    \/ (Nat.even (length p) = false /\  length M  < length (xor_edge M p)).
Proof.
  intros.
  unfold xor_edge.
  rewrite app_length.
  induction p.
  - inversion H0.
  - destruct p.
    + simpl. right. split. auto. simpl in H1. rewrite (remove_length_not a M H1).
    rewrite (list_sub_e_notIn a nil M H1). omega.
    + destruct H. assert (1<=length(e::p)). simpl. omega.
      assert(~ In (last (e :: p) de) M ). simpl. simpl in H0. auto.
      pose proof (IHp H2 H3 H4). clear H0 IHp .
      destruct H5.
       * right.  destruct H0. rewrite  (even_cons a (e::p)). rewrite H0. split.
         auto. eapply Nat.le_lt_trans. apply H5.
         apply (list_sub_length_cons_notIn a (e::p) M).
         destruct H. destruct H.
         pose proof (path_first_decide (e::p) H2 H4 H3). destruct H7. destruct H7.
         unfold Nat.odd in H7. rewrite H0 in H7. inversion H7. destruct H7.
         unfold not in H6. apply H6 in H8. inversion H8. destruct H. auto.
       * left. destruct H0. rewrite  (even_cons a (e::p)). rewrite H0. split.
         auto.
         assert (In a M).
         {
          destruct H. destruct H. auto.
          pose proof (path_first_decide (e::p) H2 H4 H3).
          destruct H6. destruct H6. destruct H. unfold not in H7. apply H7 in H8.
          inversion H8. destruct H6. unfold Nat.odd in H6. rewrite H0 in H6.
          inversion H6.
          }
         pose proof (list_sub_length_cons_In a (e::p) M H6). rewrite H7 in H5.
         apply lt_n_Sm_le. auto.
Qed.

Lemma  aug_path_odd_pre1 : forall p , aug_path_pre p -> 1<= length p.
Proof.
  intros.
  destruct p. inversion H. simpl. omega. Qed.
Lemma  aug_path_odd_pre2 : forall p , aug_path p ->  ~ In (last p de) M.
Proof.
  intros.
  unfold aug_path in H. destruct H as [ h [h1 h2]]. auto.
Qed.

Theorem aug_path_odd : forall p,
  aug_path p -> 1 <=length (p) -> ~ In (last p de) M ->  Nat.even (length p) = false.
Proof.
  intros.
  destruct p.
  inversion H.
  induction p.
  - simpl. reflexivity.
  - destruct H. destruct H2. simpl.
    assert (1<= length (a::p)). simpl. omega.
    assert ( ~ In (last (a::p) de) M). simpl. simpl in H1. auto.
    pose proof (path_first_decide (a::p) H3 H5 H4).
    assert (Nat.odd (length (a :: p)) = false). { destruct H.
    destruct H6. destruct H6. simpl in H8. unfold not in H8.
    apply H8 in H7; inversion H7. destruct H6. auto. }
    unfold Nat.odd in H7. unfold length in H7. rewrite S_even in H7.
    rewrite Bool.negb_involutive in  H7. auto.
Qed.

(*证明：根据aug_path得到的匹配确实更大*)
Theorem Bigger : forall p , 
 aug_path p ->
    length M   < length (xor_edge M p).
Proof.
  intros.
  unfold xor_edge.
  rewrite app_length.
  destruct p.
  inversion H.
  induction p.
  - unfold aug_path in H. rewrite (list_sub_e_notIn e nil M H). simpl.
   rewrite (remove_length_not e M H). omega.
  - clear IHp. assert (1<=length (e::a::p)). simpl. omega.
    pose proof (aug_path_odd (e::a::p) H H0).
    destruct H. destruct H0. destruct H. destruct H2.
    
    
    
    Admitted.




