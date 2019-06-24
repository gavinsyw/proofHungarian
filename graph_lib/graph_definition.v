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


Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.omega.Omega.
Require Import Coq.Arith.EqNat.

Arguments clos_refl_trans {A} _ _ _.
Arguments clos_refl_trans_1n {A} _ _ _.
Arguments clos_refl_trans_n1 {A} _ _ _.
Arguments PreGraph _ _ {_} {_}.

Section BiGraph.

Definition V:=nat.
Definition E := (V * V)%type.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.

Record BiGraph := {
  Vlist : list V;
  Elist : list E;
  vvalid : V -> Prop := fun x => In x Vlist;
  evalid : E -> Prop := fun e => In e Elist;
  src : E -> V := fun e => fst e;
  dst : E -> V := fun e => snd e;
  f : V -> bool ; (* 表示两个点集 *)
  re : forall e x y, evalid e -> src e = x -> dst e = y -> f x = negb (f y);
  re_a : forall e, let e2:= (snd e, fst e)in  In e2 Elist ; 
  (**每两个点之间连两条边*)
}.

(* Record BiGraph := {
  Vlist : list V;
  Elist : list E;
  vvalid : V -> Prop := fun x => In x Vlist;
  evalid : E -> Prop := fun e => In e Elist;
  src : E -> V := fun e => fst e;
  dst : E -> V := fun e => snd e;
  f : V -> bool ; (* 表示两个点集 *)
  re : forall e x y, evalid e -> src e = x -> dst e = y -> f x = negb (f y);
}. *)


Context {BG: BiGraph}.

Fixpoint Inb (x: V) (l : list V) : bool :=
match l with 
|nil => false
|y::l' => if  Nat.eqb x y then true else (Inb x l')
end. 

Definition Vstateb:= V -> bool.
Definition default_Vstateb : Vstateb := (fun _ => false).
Definition Vstateb_update (m : Vstateb) (v: V) : Vstateb :=
 fun x =>   if Nat.eqb x  v then true else m x.
Definition Vstateb_update_f (m : Vstateb) (v: V) : Vstateb :=
 fun x =>  if Nat.eqb x  v then false else m x.

Definition Vstateb_update_l (m : Vstateb) (v : list V) : Vstateb :=
 fun x => if Inb x v then true else m x.
Definition Vstateb_update_fl (m : Vstateb) (v : list V) : Vstateb :=
 fun x => if Inb x v then false else m x .

Definition Vstateb_update_op (m : Vstateb) (v : option V) : Vstateb :=
fun x => match v with 
       |None => m x 
       |Some y => Vstateb_update m y  x
       end.
(* Definition Vstate:= V -> Prop.
Definition default_Vstate : Vstate := (fun _ => False).
Definition Vstate_update (m : Vstate) (v: V) : Vstate :=
 fun x =>   x =  v \/ m x.
Definition Vstate_update_f (m : Vstate) (v: V) : Vstate :=
 fun x =>  ( x = v -> False ) \/ (~ x = v  -> m x).

Definition Vstate_update_l (m : Vstate) (v : list V) : Vstate :=
 fun x => In x v \/ m x.

Definition Vstate_update_fl (m : Vstate) (v : list V) : Vstate :=
 fun x => (In x v -> False ) \/ (~ In  x  v  -> m x).
 *)
Definition matching := list E.



Fixpoint list_sub (u v :list V) : list V :=
match v with 
|nil => u
|e::v' => list_sub (remove EV e u ) v'
end.

Fixpoint list_sub_e (u v :list E) : list E :=
match v with 
|nil => u
|e::v' => list_sub_e (remove EE e u ) v'
end.

Fixpoint e_to_v' (g : BiGraph) (p : list E) {struct p} :
  list V :=
  match p with
  | nil => nil
  | e :: nil =>
      src g e :: dst g e :: nil
  | e :: (_ :: _) as el =>
      src g e :: e_to_v' g el
  end.

Fixpoint e_to_vth (g: BiGraph) (p : list E) {struct p} : list V :=
  match p with
  | nil => nil
  | e :: nil => dst g e :: src g e :: nil
  | e :: el => dst g e :: e_to_v' g el
  end.
Inductive step  : V -> V -> Prop :=
|step_intro : forall e  x y ,
                 evalid BG e ->
                 src BG e = x ->
                 dst BG e = y -> step  x y.

Inductive connected (v: V) (cl : list V) : Prop :=
|connected_intro : forall (x : V ), ( step  v x <-> In x cl) -> connected v cl .

(*  给出图的点集  *)

Definition  LV:= Vlist BG.
(* Hypothesis lise_re : forall v , In v LV <-> vvalid BG v.
 *)
Definition get_connectednode_func  := V -> list V.
Definition LE:= Elist BG.

(* Variable con : V -> list V. (* TODO : 怎么得到一个点的连接点集 *) *)
Fixpoint con (v: V) (all_e: list E) : list V :=
match all_e with
|nil => nil
|e::all_e' => if (eq_nat_dec (fst e) v) then (snd e)::con v all_e'
    else con v all_e'
end.

Hypothesis conlistre : forall v , connected v (con v LE).


Definition e_to_v (p : list E) : list V := e_to_vth BG p .

Fixpoint Ma (v : V) (M :matching): (option V) := 
match M with 
|nil => None
|e::m' => if Nat.eqb (src BG e) v then 
          Some (dst BG e) else 
            (Ma v m')
end.


Context {M : matching}.

Definition Matching (v: V) : (option V) := Ma v M.
Definition path : Type := (V * list E)%type.


(* Definition crossGraph (matching) : Type :=  PreGraph 

 *)

Print Nat.odd.

Definition Max := length(LV).


(* 找到对于一个Vstateb中从大到小的*)
Print nth_In.
Fixpoint conn (v: V) (v1 : Vstateb) (n:nat): V :=
match n with
|O => O
|S n' =>  if Inb (S n') (con v LE) then 
             (if v1 (S n') then n else conn v v1 n')
             else conn v v1 n'
end.

Definition max_conn (v : V) (v1 : Vstateb) := conn v v1 Max.


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
           cross_step (v1, (u, e1::(e2::(e3::p)))) ( Vstateb_update_fl v1 (list_sub (con u LE) (e_to_v p) ) , (w2 ,e3::p))
(**回溯到上一个匹配点*) 
|Back_to_no : forall (u w1 w2 : V) (e1 e2 : E) (p : list E )
              (v1 : Vstateb) ,
     v1 u = true -> max_conn u v1 = O -> 
           In e1 M ->  ~In e2 M -> 
             src BG e1 = w1 -> dst BG e1 = u  -> src BG e2 = w2 -> dst BG e2 = w1 ->
           cross_step (v1, (u, e1::(e2::nil))) ( Vstateb_update_fl v1 (list_sub (con u LE)(e_to_v p) ) , (w2 ,nil))
(** 回溯到初始状态即一个点*)    .



Inductive cross_halt : (Vstateb * path) -> Prop :=
|success : forall (u : V) (v : Vstateb) (e : E )(p : list E),
              Matching u = None ->
            v u = true -> dst BG e = u -> ~ In e M -> cross_halt (v , (u, e::p)).
Definition state := (Vstateb * path)%type.
Definition multi_cstep : state -> state -> Prop := clos_refl_trans cross_step .


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


Variable de : E.

(**定义
  交错路
  增广路*)
Fixpoint cross_path (l: list E) : Prop :=
match l with
|nil => True
|m::nil => True
|m::l' => (* actually hd de l' 不会需要default值*)
             ( In m M /\ ~ In (hd de l') M  \/ 
                   ~ In m M /\  In (hd de l') M)
             /\ cross_path l'
end.


Definition aug_path (l: list E) : Prop :=
match l with 
|nil => False
|m::nil => ~ In m M
|m::n::l' => (~ In m M /\ In n M )/\ 
          (cross_path l' /\ cross_path (n::l')) 
end.

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
  forall (p: list E) (v: V) st, aug_path p -> cross_halt st -> multi_cstep (Vstateb_update default_Vstateb v, (v, nil)) st -> Matching (fst (snd st)) = None.
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
          aug_path p.
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
Theorem step_to_aug: forall v st, cross_halt st ->
     multi_cstep ( Vstateb_update default_Vstateb v, (v, nil)) st ->
       aug_path (snd (snd st)) .
Proof.
  intros.
  eapply (path_to_aug (snd (snd st))).
  eapply cross_stay. 2: apply H0. reflexivity.
  eapply cross_start. auto. apply H0.
  eapply path_odevity. auto. apply H0.
Qed.

Definition xor_edge (e1 p: list E) : list E :=
  list_sub_e e1 p ++ list_sub_e p e1.

Lemma cross_more_match: forall p a m, 
  cross_path p -> a::m = M -> length (list_sub_e m p) + length (list_sub_e p m) <= length (list_sub_e (a :: m) p) + length (list_sub_e (remove EE a p) m).
Proof.
  intros.
  induction p.
  simpl. omega.
  destruct p.
  unfold remove.
  destruct (EE a a0).
  unfold list_sub_e at 1 3.
  unfold Equivalence.equiv in e.
  rewrite <- e.
  simpl.
  destruct (EE a a).
  assert (length (list_sub_e (a :: nil) m) <= length (list_sub_e nil m)).
  admit.
  omega.
  simpl.
  pose proof classic (In a m).
  destruct H1.
  
  
  destruct list_sub_e at 2.
  destruct length at 4.
  pose proof classic (In a0 m).
  Admitted.
  
  
(*证明：根据aug_path得到的匹配确实更大*)
Theorem Bigger : forall p , 
 aug_path p ->
    length M   < length (xor_edge M p).
Proof.
  intros.
  unfold xor_edge.
  rewrite app_length.
  induction M.
  simpl.
  assert (length p > 0).
  induction p. destruct H. simpl. omega.
  omega.
  simpl.
  
  Admitted.


Lemma match_smaller: forall v a m, Ma v (a :: m) = None -> Ma v m = None /\ v <> fst a /\ v <> snd a.
Proof.
  intros.
  unfold Ma in H.
  destruct (src BG a =? v).
  inversion H.
  split.
  + auto.
  + split.
Admitted.

Print nodup.

Definition disjoint_edges (e1 e2 : E) : Prop :=
  ((fst e1) <> (fst e2)) /\ ((fst e1) <> (snd e2)) /\ ((snd e1) <> (fst e2)) /\ ((snd e1) <> (snd e2)).

Definition disjoint_edges_set (l:list E) : Prop :=
  forall e1 e2: E,
  In e1 l -> In e2 l -> e1 <> e2 -> disjoint_edges e1 e2.

Definition is_matching (m: list E): Prop :=
disjoint_edges_set m /\ forall e, In e m -> In e (Elist BG).

Theorem greater_match_to_aug_path:
  forall m v, is_matching m -> is_matching M -> length m > length M -> Ma v m <> None -> Ma v M = None -> exists st, (multi_cstep (Vstateb_update default_Vstateb v, (v, nil)) st -> cross_halt st).
Proof.
  intros.
  unfold is_matching in H.
  destruct H.
  unfold disjoint_edges_set in H.
Admitted.

Lemma nonmatching_to_aug_exist:
  forall v v', Matching v = None -> In v' (con v LE) -> Matching v' = None -> aug_path ((v, v')::nil).
Proof.
  intros.
  unfold aug_path.
  unfold Matching in H.
  unfold Matching in H1.
  induction M.
  + unfold In. auto.
  + unfold Ma in H.
    apply match_smaller in H.
    apply match_smaller in H1.
    
  
   induction a.
    unfold Ma in H.
    
    unfold src in H.
    unfold fst in H.
    
    simpl in H.
    induction a.
    destruct H1.
  unfold Ma in H.
Admitted.

Lemma nonmatching_to_aug :
  forall v, Matching v = None -> (exists st, cross_halt st ->
     multi_cstep (Vstateb_update default_Vstateb v, (v, nil)) st).
Proof.
  intros.
  + Admitted.






End BiGraph.


(* *)



  












