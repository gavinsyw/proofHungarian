Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import RamifyCoq.Coqlib.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.msl_ext.iter_sepcon.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.subgraph2.
Require RamifyCoq.graph.marked_graph. Import RamifyCoq.graph.marked_graph.MarkGraph.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.data_structure.general_spatial_graph.
Require Import Coq.Logic.Classical.
Import RamifyCoq.msl_ext.seplog.OconNotation.

Local Open Scope logic.

Class BasicMarkProgramSetting: Type := {
  addr: Type;
  null: addr;
  pred: Type;
  eDV: Type;
  SGBA: SpatialGraphBasicAssum addr (addr * nat)
}.

Class ForwardListGraph {V: Type} {VE: EqDec V eq} {EE: EqDec (V * nat) eq} (G: PreGraph V (V * nat)) : Type := {
  flg_sound: forall v n, src G (v, n) = v;
  flg_complete: forall v e, src G e = v -> fst e = v
}.

Class MixListGraph {V: Type} {VE: EqDec V eq} {EE: EqDec (V * nat) eq} {cDV eDV: Type} (G: PreGraph V (V * nat))
  (vlabel: V -> (cDV * (nat -> option eDV))) : Type := {
  sz: V -> nat;
  mg_consistent: forall v n, snd (vlabel v) n = None \/ ~ evalid G (v, n);
  mg_complete: forall v n, n < sz v -> snd (vlabel v) n <> None \/ evalid G (v, n);
  mg_bounded: forall v n, n >= sz v -> snd (vlabel v) n = None /\ ~ evalid G (v, n)
}.

Arguments sz {_} {_} {_} {_} {_} _ _ _ _.

Existing Instance SGBA.

Section SpatialGraphForMark.

Context {BMPS: BasicMarkProgramSetting}.

Class MixMaFin (g: PreGraph addr (addr * nat)) (vlabel: addr -> (bool * addr * (nat -> option eDV))) := {
  fl: ForwardListGraph g;
  mix: MixListGraph g vlabel;
  ma: MathGraph g;
  fin: FiniteGraph g;
  is_null_def': forall x: addr, is_null g x = (x = null)
}.

Definition Graph := (GeneralGraph addr (addr * nat) (bool * addr * (nat -> option eDV)) unit (fun g vlabel _ => MixMaFin g vlabel)).

Identity Coercion G_GG : Graph >-> GeneralGraph.

Instance MGS: MarkGraphSetting (bool * addr * (nat -> option eDV)).
  apply (Build_MarkGraphSetting (bool * addr * (nat -> option eDV))
          (fun d => fst (fst d) = true)
          (fun d => (true, snd (fst d), snd d))
          (fun d => (false, snd (fst d), snd d)));
  intros.
  + destruct x as [[? ?] ?]. destruct b; [left | right]; simpl; congruence.
  + auto.
  + destruct x as [[? ?] ?]. simpl; congruence.
Defined.

Fixpoint mergeMixList (v: addr) (d: nat -> option eDV) (dst: addr * nat -> addr) (init n: nat) : list (sum addr eDV) :=
  match n with
  | O => nil
  | S n' =>
     match d init with
     | None => inl (dst (v, init))
     | Some dv => inr dv
     end :: mergeMixList v d dst (S init) n'
  end.

Instance flGraph (G: Graph): ForwardListGraph G :=
  @fl G _ (@sound_gg _ _ _ _ _ _ _ G).

Instance mixGraph (G: Graph): MixListGraph G (vlabel G) :=
  @mix G _ (@sound_gg _ _ _ _ _ _ _ G).

Instance maGraph(G: Graph): MathGraph G :=
  @ma G _ (@sound_gg _ _ _ _ _ _ _ G).

Instance finGraph (G: Graph): FiniteGraph G :=
  @fin G _ (@sound_gg _ _ _ _ _ _ _ G).

Definition is_null_def (g: Graph): forall x: addr, is_null g x = (x = null) := is_null_def'.

Definition mixgraph_len (g: Graph) (x: addr) := @sz _ _ _ _ _ g (vlabel g) _ x.

Definition gamma (G : Graph) (v: addr) : bool * addr * list (sum addr eDV) :=
  (fst (vlabel G v), mergeMixList v (snd (vlabel G v)) (dst G) 0 (mixgraph_len G v)).

Instance RGF (G: Graph): ReachableFiniteGraph G.
  apply Build_ReachableFiniteGraph.
  intros.
  apply finite_reachable_computable in H.
  + destruct H as [l [? ?]].
    exists l; auto.
  + apply maGraph.
  + apply (LocalFiniteGraph_FiniteGraph G), finGraph.
  + apply (FiniteGraph_EnumCovered G), finGraph.
Defined.

Lemma Graph_reachable_by_unmarked_dec: forall (G: Graph) x, Decidable (vvalid G x) -> ReachDecidable G x (unmarked G).
Proof.
  intros.
  intro y.
  apply reachable_by_decidable; auto.
  + apply maGraph.
  + apply LocalFiniteGraph_FiniteGraph, finGraph.
  + apply FiniteGraph_EnumCovered, finGraph.
Qed.

Definition Graph_SpatialGraph (G: Graph): SpatialGraph addr (addr * nat) (bool * addr * list (sum addr eDV)) unit := Build_SpatialGraph _ _ _ _ _ _ G (gamma G) (fun _ => tt).

Coercion Graph_SpatialGraph: Graph >-> SpatialGraph.

Lemma weak_valid_vvalid_dec: forall (g : Graph) (x: addr),
  weak_valid g x -> {vvalid g x} + {~ vvalid g x}.
Proof.
  intros.
  apply null_or_valid in H.
  destruct H; [right | left]; auto.
  pose proof valid_not_null g x; tauto.
Qed.

Definition Graph_gen (G: Graph) (x: addr) (marking: bool) : Graph.
  refine (generalgraph_gen G x (match vlabel G x with (b, m, d) => (marking, m, d) end) _).
  refine (Build_MixMaFin _ _ (@fl _ _ (sound_gg G)) _ (@ma _ _ _) (@fin _ _ (sound_gg G)) (@is_null_def' _ _ (sound_gg G))).
  refine (Build_MixListGraph _ _ _ _ _ _ _ (@sz _ _ _ _ _ _ _ (@mix _ _ (sound_gg G))) _ _ _); intros.
  + destruct (vlabel G x) as [[b m] d] eqn:H.
    unfold update_vlabel.
    destruct_eq_dec x v; [subst |]; simpl.
    - change d with (snd (b, m, d)); rewrite <- H. apply mg_consistent.
    - apply mg_consistent.
  + rename H into H0; destruct (vlabel G x) as [[b m] d] eqn:H.
    unfold update_vlabel.
    destruct_eq_dec x v; [subst |]; simpl.
    - change d with (snd (b, m, d)); rewrite <- H. apply mg_complete; auto.
    - apply mg_complete; auto.
  + rename H into H0; destruct (vlabel G x) as [[b m] d] eqn:H.
    unfold update_vlabel.
    destruct_eq_dec x v; [subst |]; simpl.
    - change d with (snd (b, m, d)); rewrite <- H. apply mg_bounded; auto.
    - apply mg_bounded; auto.
Defined.

Lemma Graph_gen_spatial_spec: forall (G: Graph) (x: addr) (b b': bool) m d,
  vgamma G x = (b, m, d) ->
  (Graph_gen G x b') -=- (spatialgraph_gen G x (b', m, d)).
Proof.
  intros.
  split; [reflexivity | split; [| auto]].
  simpl in *; intros.
  unfold gamma in *; simpl in *; unfold update_vlabel.
  destruct_eq_dec x v; subst.
  + destruct (vlabel G v) as [[b0 m0] d0].
    destruct G; simpl in H; destruct sound_gg.
    destruct mix0.
    inversion H; subst; f_equal; f_equal.
  + destruct (vlabel G v) as [[b0 m0] d0].
    destruct G; simpl in H; destruct sound_gg.
    destruct mix0.
    auto.
Qed.

Lemma Graph_gen_true_mark1: forall (G: Graph) (x: addr) m d,
  vgamma G x = (false, m, d) ->
  vvalid G x ->
  mark1 G x (Graph_gen G x true).
Proof.
  intros.
  split; [| split; [| split]].
  + reflexivity.
  + auto.
  + simpl.
    unfold update_vlabel; simpl.
    destruct_eq_dec x x; [| congruence].
    simpl in H.
    unfold gamma in H.
    destruct (vlabel G x) as [[? ?] ?]; reflexivity.
  + intros.
    simpl.
    unfold update_vlabel; simpl.
    destruct_eq_dec x n'; [congruence |].
    reflexivity.
Qed.

Lemma weak_valid_si: forall (g1 g2: Graph) n, g1 ~=~ g2 -> (weak_valid g1 n <-> weak_valid g2 n).
Proof.
  intros.
  unfold weak_valid.
  rewrite !is_null_def.
  destruct H as [? _].
  rewrite H.
  reflexivity.
Qed.

Ltac s_rewrite p :=
  let H := fresh "H" in
  pose proof p as H;
  simpl in H;
  rewrite H;
  clear H.

Fixpoint left_list {A B: Type} (xs: list (sum A B)) : list A :=
  match xs with
  | nil => nil
  | inl x :: xs => x :: left_list xs
  | inr _ :: xs => left_list xs
  end.

Lemma inl_in: forall {A B: Type} (xs: list (sum A B)) x,
  In (inl x) xs <-> In x (left_list xs).
Proof.
  intros.
  induction xs.
  + simpl; tauto.
  + destruct a.
    - simpl.
      assert (a = x <-> inl a = (inl x: sum A B)) by (split; intro HH; [subst | inversion HH]; auto).
      tauto.
    - simpl.
      assert (~ inr b = inl x) by congruence.
      tauto.
Qed.    

Lemma In_left_list_mergeMixList: forall (g: Graph) x y (init len: nat),
  init + len = mixgraph_len g x ->
  (In y (left_list (mergeMixList x (snd (vlabel g x)) (dst g) init len)) <->
   exists n, init <= n < init + len /\ evalid g (x, n) /\ dst g (x, n) = y).
Proof.
  intros.
  revert init H; induction len; intros.
  + simpl.
    split; [tauto |].
    intros [n [? [? ?]]].
    omega.
  + simpl.
    destruct (snd (vlabel g x) init) eqn: HH.
    - rewrite (IHlen (S init)) by omega; clear IHlen.
      split; intros [n [? [? ?]]]; exists n; (split; [| auto]).
      * omega.
      * destruct (eq_nat_dec n init); [| omega].
        subst.
        exfalso.
        pose proof @mg_consistent _ _ _ _ _ g (vlabel g) (@mix _ _ (sound_gg g)) x init.
        rewrite HH in H2.
        assert (Some e <> None) by congruence; tauto.
    - simpl In.
      rewrite (IHlen (S init)) by omega; clear IHlen.
      split; [intros [? | [n [? [? ?]]]] | intros [n [? [? ?]]]].
      * exists init; split; [omega |].
        split; [| auto].
        pose proof @mg_complete _ _ _ _ _ g (vlabel g) (@mix _ _ (sound_gg g)) x init.
        unfold mixgraph_len in H.
        spec H1; [unfold mixGraph in H; omega |].
        tauto.
      * exists n.
        split; [omega | auto].
      * destruct (eq_nat_dec n init); [left; subst; auto | right].
        exists n.
        split; [omega | auto].
Qed.

Lemma gamma_step: forall (g : Graph) x b m d, vvalid g x -> vgamma g x = (b, m, d) -> forall y, step g x y <-> In y (left_list d).
Proof.
  intros. simpl in H0; unfold gamma in H0. inversion H0; subst.
  clear H0 H2.
  rewrite In_left_list_mergeMixList by omega.
  rewrite step_spec; split; intros.
  + destruct H0 as [? [? [? ?]]].
    pose proof @flg_complete _ _ _ g (flGraph g) x x0 H1.
    destruct x0 as [xx n]; simpl in H3; subst xx.
    exists n.
    split; [| auto].
    pose proof @mg_bounded _ _ _ _ _ g _ (mixGraph g) x n.
    pose proof @mg_consistent _ _ _ _ _ g _ (mixGraph g) x n.
    unfold mixgraph_len.
    destruct (lt_dec n (sz g (vlabel g) (mixGraph g) x)).
    - omega.
    - spec H3; [omega |].
      tauto.
  + destruct H0 as [n [? [? ?]]].
    exists (x, n).
    repeat split; auto.
    apply flg_sound.
Qed.

Lemma gamma_nth_weak_valid: forall (g : Graph) x b m d n y, vvalid g x -> vgamma g x = (b, m, d) -> nth_error d n = Some (inl y) -> weak_valid g y.
Proof.
  intros.
  assert (mergeMixList x (snd (vlabel g x)) (dst g) 0 (mixgraph_len g x) = d) by (inversion H0; auto).
  apply Coqlib.nth_error_in in H1; clear n.
  rewrite <- H2 in H1.
  apply inl_in in H1.
  rewrite In_left_list_mergeMixList in H1; [| omega].
  destruct H1 as [n [? [? ?]]].
  pose proof valid_graph g (x, n).
  pose proof @flg_sound _ _ _ g _ x n.
  rewrite H4, H6 in H5.
  tauto.
Qed.

(*
Lemma gamme_true_mark: forall (g g': Graph) x y m d, Decidable (vvalid g y) -> vgamma g x = (true, m, d) -> mark g y g' -> vgamma g' x = (true, m, d).
Proof.
  intros.
  simpl in H0 |- *.
  unfold gamma in H0 |- *.
  destruct (vlabel g x) as [[ga1 ga2] ga3].
  inversion H0; subst ga1; subst ga2.
  pose proof mark_marked g y g' H1.
  spec H2; [apply Graph_reachable_by_unmarked_dec; auto |].
  specialize (H2 x).
  simpl in H2.
  spec H2; [rewrite H3; auto |].
  rewrite <- H2.
  destruct H1 as [[_ [_ [_ ?]]] _].
  rewrite !H1.
  auto.
Qed.

Lemma mark1_mark_left_mark_right: forall (g1 g2 g3 g4: Graph) root l r,
  vvalid g1 root ->
  vvalid g2 root ->
  vgamma g1 root = (false, l, r) ->
  vgamma g2 root = (true, l, r) ->
  vgamma g3 root = (true, l, r) ->
  mark1 g1 root g2 ->
  mark g2 l g3 ->
  mark g3 r g4 ->
  mark g1 root g4.
Proof.
  intros.
  apply (mark1_mark_list_mark g1 root (l :: r :: nil) g2); auto.
  + intros; apply Graph_reachable_by_unmarked_dec.
    destruct_eq_dec x l; [| destruct_eq_dec x r; [| exfalso]].
    - subst; eapply weak_valid_vvalid_dec, gamma_left_weak_valid; eauto.
    - subst; eapply weak_valid_vvalid_dec, gamma_right_weak_valid; eauto.
    - destruct H7 as [| [|]]; try congruence; inversion H7.
  + intros.
    destruct_eq_dec x l; [| destruct_eq_dec x r; [| exfalso]].
    - subst; eapply weak_valid_vvalid_dec, gamma_left_weak_valid; eauto.
    - subst; eapply weak_valid_vvalid_dec, gamma_right_weak_valid; eauto.
    - destruct H7 as [| [|]]; try congruence; inversion H7.
  + apply Graph_reachable_by_unmarked_dec.
    left; auto.
  + unfold unmarked; rewrite negateP_spec.
    simpl in H1 |- *.
    inversion H1.
    destruct (vlabel g1 root); congruence.
  + unfold step_list.
    intros y.
    rewrite gamma_step by eauto.
    simpl.
    pose proof (@eq_sym _ l y).
    pose proof (@eq_sym _ r y).
    pose proof (@eq_sym _ y l).
    pose proof (@eq_sym _ y r).
    tauto.
  + repeat (econstructor; eauto).
Qed.

Context {SGP: SpatialGraphPred addr (addr * LR) (bool * addr * addr) unit pred}.
Context {SGA: SpatialGraphAssum SGP}.

Local Open Scope logic.

Instance complement_proper (V: Type): Proper ((pointwise_relation V iff) ==> (pointwise_relation V iff)) (Complement V).
  hnf; intros.
  hnf; intros.
  unfold Complement, Ensembles.In.
  specialize (H a).
  tauto.
Defined.

Lemma graph_ramify_aux1: forall (g: Graph) (x l: addr)
  {V_DEC: Decidable (vvalid g l)},
  vvalid g x ->
  Included (reachable g l) (reachable g x) ->
  (graph x g: pred) |-- graph l g *
   ((EX g': Graph, !! mark g l g' && graph l g') -*
    (EX g': Graph, !! mark g l g' && graph x g')).
Proof.
  intros.
  apply graph_ramify_aux1; auto.
  + apply RGF.
  + intros; apply RGF.
  + intros g' ?.
    split; [split |].
    - destruct H1 as [[? _] _].
      rewrite <- H1; auto.
    - destruct H1 as [? _].
      intro; unfold Ensembles.In; rewrite <- H1.
      apply H0.
    - split; [| split].
      * destruct H1 as [H1 _].
        unfold unreachable_partial_spatialgraph.
        simpl; rewrite H1.
        reflexivity.
      * intros; simpl in *.
        destruct H1 as [? [_ ?]].
        specialize (H4 v).
        destruct H2; unfold Complement, Ensembles.In in H5; rewrite reachable_through_set_single in H5.
        spec H4; [intro HH; apply reachable_by_is_reachable in HH; auto |].
        unfold gamma; simpl in H4.
        destruct H1 as [? [? [? ?]]].
        assert (true <> false) by congruence.
        assert (false <> true) by congruence.
        destruct (vlabel g v), (vlabel g' v); simpl in H4.
        1: rewrite !H8; auto.
        1: tauto.
        1: tauto.
        1: rewrite !H8; auto.
      * intros; simpl; auto.
Qed.

Lemma gamma_left_reachable_included: forall (g: Graph) x d l r,
                                       vvalid g x -> vgamma g x = (d, l, r) -> Included (reachable g l) (reachable g x).
Proof.
  intros. intro y; intros. apply reachable_by_cons with l; auto. split; auto. split.
  + apply reachable_head_valid in H1; auto.
  + rewrite (gamma_step _ _ _ _ _ H H0). auto.
Qed.

Lemma gamma_right_reachable_included: forall (g: Graph) x d l r,
                                        vvalid g x -> vgamma g x = (d, l, r) -> Included (reachable g r) (reachable g x).
Proof.
  intros. intro y; intros. apply reachable_by_cons with r; auto. split; auto. split.
  + apply reachable_head_valid in H1; auto.
  + rewrite (gamma_step _ _ _ _ _ H H0). auto.
Qed.

Lemma graph_ramify_aux1_left: forall (g: Graph) x d l r,
  vvalid g x ->
  vgamma g x = (d, l, r) ->
  (graph x g: pred) |-- graph l g *
   ((EX g': Graph, !! mark g l g' && graph l g') -*
    (EX g': Graph, !! mark g l g' && graph x g')).
Proof.
  intros.
  apply graph_ramify_aux1; auto.
  + pose proof (gamma_left_weak_valid g x d l r H H0).
    apply weak_valid_vvalid_dec; auto.
  + eapply gamma_left_reachable_included; eauto.
Qed.

Lemma graph_ramify_aux1_right: forall (g: Graph) x d l r,
  vvalid g x ->
  vgamma g x = (d, l, r) ->
  (graph x g: pred) |-- graph r g *
   ((EX g': Graph, !! mark g r g' && graph r g') -*
    (EX g': Graph, !! mark g r g' && graph x g')).
Proof.
  intros.
  apply graph_ramify_aux1; auto.
  + pose proof (gamma_right_weak_valid g x d l r H H0).
    apply weak_valid_vvalid_dec; auto.
  + eapply gamma_right_reachable_included; eauto.
Qed.
*)

End SpatialGraphForMark.