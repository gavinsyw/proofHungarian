Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import RamifyCoq.Coqlib.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.marked_graph.
Require Import RamifyCoq.graph.graph_gen.

Section STATE_MACHINE.

Context {V E: Type}.
Variable G: PreGraph V E.
Notation Marking := (NodePred G).

Inductive State: Type :=
  | EnterNode: list V -> Marking -> State
  | InNode: list V -> Marking -> State
  | LeaveNode: list V -> Marking -> State
  | ForwardEdge: list V -> E -> Marking -> State.

Definition marking_of_state (st: State): Marking :=
  match st with
  | EnterNode _ m => m
  | InNode _ m => m
  | LeaveNode _ m => m
  | ForwardEdge _ _ m => m
  end.

Definition chain_of_state (st: State): list V :=
  match st with
  | EnterNode vs _ => vs
  | InNode vs _=> vs
  | LeaveNode vs _ => vs
  | ForwardEdge vs _ _ => vs
  end.

Inductive at_node: State -> V -> Prop :=
  | at_node_EnterNode: forall v vs m, at_node (EnterNode (v :: vs) m) v
  | at_node_InNode: forall v vs m, at_node (InNode (v :: vs) m) v
  | at_node_LeaveNode: forall v vs m, at_node (LeaveNode (v :: vs) m) v
  | at_node_ForwardEdge: forall v vs e m, at_node (ForwardEdge (v :: vs) e m) v
  .

Definition using_edge (e: E) (st: State): Prop :=
  match st with
  | EnterNode _ _ 
  | InNode _ _ 
  | LeaveNode _ _ => False
  | ForwardEdge _ e0 _ => e = e0
  end.

Definition used_in_past (e: E) (s: list State): Prop :=
  exists st, In st s /\ using_edge e st.

Section HISTORY.

Variables (root: V) (m_init: Marking).

Instance MG (m: Marking): MarkedGraph V E := Build_MarkedGraph _ _ G m.

Inductive History : list State -> Prop :=
  | EmptyHistory: History (EnterNode (root :: nil) m_init :: nil)
  | EnterUnmarkedNode: forall v vs m m' h,
      History (EnterNode (v :: vs) m :: h) ->
      vvalid v ->
      (negateP m) v ->
      mark1 (MG m) v (MG m') ->
      History (InNode (v :: vs) m' :: EnterNode (v :: vs) m :: h)
  | EnterMarkedNode: forall v vs m h,
      History (EnterNode (v :: vs) m :: h) ->
      (~ vvalid v \/ m v) ->
      History (LeaveNode (v :: vs) m :: EnterNode (v :: vs) m :: h)
  | StepForward: forall v vs e m h,
      History (InNode (v :: vs) m :: h) ->
      src e = v ->
      evalid e ->
      ~ used_in_past e h ->
      History (ForwardEdge (v :: vs) e m :: InNode (v :: vs) m :: h)
  | LeaveAfterForward: forall v vs m h,
      History (InNode (v :: vs) m :: h) ->
      (forall e, src e = v -> evalid e -> used_in_past e h) ->
      History (LeaveNode (v :: vs) m :: InNode (v :: vs) m :: h)
  | DoForward: forall v vs e m h,
      History (ForwardEdge vs e m :: h) ->
      dst e = v ->
      vvalid v ->
      History (EnterNode (v :: vs) m :: ForwardEdge vs e m :: h)
  | DoLeave: forall v vs m h,
      History (LeaveNode (v :: vs) m :: h) ->
      History (InNode vs m :: LeaveNode (v :: vs) m :: h).

Lemma History_cons_rev: forall st h,
  History (st :: h) ->
  h = nil \/ History h.
Proof.
  intros.
  inversion H; [left | right ..]; auto.
Qed.

Lemma partial_History_rev: forall h h',
  History (h ++ h') ->
  h' = nil \/ History h'.
Proof.
  intros.
  induction h.
  + right; auto.
  + simpl in H.
    apply History_cons_rev in H.
    destruct H.
    - left.
      destruct h, h'; try inversion H; auto.
    - tauto.
Qed.

Lemma unvisited_unmarked: forall v h,
  (negateP m_init) v ->
  History h ->
  (forall st, In st h -> ~ at_node st v) ->
  (forall st, In st h -> (negateP (marking_of_state st)) v).
Proof.
  intros v h ? ? ?.
  rewrite <- Forall_forall in *.
  induction H0.
  + repeat constructor.
    auto.
  + spec IHHistory; [inversion H1; subst; auto |].
    constructor; [| auto].
    inversion H1; subst.
    assert (v0 <> v) by (intro; apply H7; subst; constructor).
    inversion IHHistory; subst.
    simpl marking_of_state in *.
    clear - H10 H4 H5.
    rewrite !@negateP_spec in *.
    destruct H4 as [_ [_ [_ ?]]].
    specialize (H v).
    tauto.
  + spec IHHistory; [inversion H1; subst; auto |].
    constructor; [| auto].
    inversion IHHistory; subst; auto.
  + spec IHHistory; [inversion H1; subst; auto |].
    constructor; [| auto].
    inversion IHHistory; subst; auto.
  + spec IHHistory; [inversion H1; subst; auto |].
    constructor; [| auto].
    inversion IHHistory; subst; auto.
  + spec IHHistory; [inversion H1; subst; auto |].
    constructor; [| auto].
    inversion IHHistory; subst; auto.
  + spec IHHistory; [inversion H1; subst; auto |].
    constructor; [| auto].
    inversion IHHistory; subst; auto.
Qed.

Lemma visited_decidable: forall v h,
  (exists st, In st h /\ at_node st v) \/ (~ exists st, In st h /\ at_node st v).
Proof.
  intros.
  apply exists_list_weak_dec.
  intros.
  destruct x; 
    (destruct l as [| hd tl]; [right | destruct (t_eq_dec hd v); [left | right]];
     [intro; inversion H | subst; constructor | intro; inversion H; congruence]).
Qed.

Lemma in_chain_visited: forall v st h,
  History h ->
  In st h ->
  In v (chain_of_state st) ->
  exists st, In st h /\ at_node st v.
Proof.
  intros.
  induction h as [| st0 h]; [inversion H0 |].
  destruct H0.
  Focus 2. {
    apply History_cons_rev in H; destruct H; [subst; inversion H0 |].
    do 2 (spec IHh; [auto |]).
    destruct IHh as [st1 [? ?]].
    exists st1; simpl; auto.
  } Unfocus.
  subst st0.
  clear IHh.
  remember (st :: h) as h0; revert st h H1 Heqh0; induction H; intros; inversion Heqh0; subst.
  + simpl chain_of_state in H1.
    simpl in H1; destruct H1; [subst v | tauto].
    exists (EnterNode (root :: nil) m_init); split; [left; auto | constructor].
  + pose proof IHHistory (EnterNode (v0 :: vs) m) h H3 eq_refl; clear IHHistory.
    destruct H4 as [st [? ?]]; exists st; split; [right |]; auto.
  + pose proof IHHistory (EnterNode (v0 :: vs) m) h H1 eq_refl; clear IHHistory.
    destruct H2 as [st [? ?]]; exists st; split; [right |]; auto.
  + pose proof IHHistory (InNode (src e :: vs) m) h H3 eq_refl; clear IHHistory.
    destruct H0 as [st [? ?]]; exists st; split; [right |]; auto.
  + pose proof IHHistory (InNode (v0 :: vs) m) h H1 eq_refl; clear IHHistory.
    destruct H2 as [st [? ?]]; exists st; split; [right |]; auto.
  + destruct H2.
    - exists (EnterNode (dst e :: vs) m); split; [left; auto | subst; constructor].
    - pose proof IHHistory (ForwardEdge vs e m) h H0 eq_refl; clear IHHistory.
      destruct H2 as [st [? ?]]; exists st; split; [right |]; auto.
  + pose proof IHHistory (LeaveNode (v0 :: vs) m) h (or_intror H1) eq_refl; clear IHHistory.
    destruct H0 as [st [? ?]]; exists st; split; [right |]; auto.
Qed.

Lemma first_visit_unmarked: forall v st h,
  (negateP m_init) v ->
  History (st :: h) ->
  (~ exists st, In st h /\ at_node st v) ->
  at_node st v ->
  exists vs m, st = EnterNode (v :: vs) m /\ (negateP m) v.
Proof.
  intros until h. intros neg_mark; intros.
  remember (st :: h) as h0; inversion H; subst.
  + inversion H2; subst.
    inversion H1; subst.
    subst; simpl marking_of_state.
    eauto.
  + inversion H6; subst.
    inversion H1; subst.
    exfalso; apply H0.
    eexists; split; [left; reflexivity | constructor].
  + inversion H4; subst.
    inversion H1; subst.
    exfalso; apply H0.
    eexists; split; [left; reflexivity | constructor].
  + inversion H6; subst.
    inversion H1; subst.
    exfalso; apply H0.
    eexists; split; [left; reflexivity | constructor].
  + inversion H4; subst.
    inversion H1; subst.
    exfalso; apply H0.
    eexists; split; [left; reflexivity | constructor].
  + inversion H5; subst.
    assert ((negateP (marking_of_state (ForwardEdge vs e m))) v).
    Focus 1. {
      apply unvisited_unmarked with (ForwardEdge vs e m :: h1); auto.
      intros; intro.
      apply H0; exists st; auto.
      left; auto.
    } Unfocus.
    inversion H1; subst.
    eauto.
  + inversion H3; subst.
    assert ((negateP (marking_of_state (LeaveNode (v0 :: vs) m))) v).
    Focus 1. {
      apply unvisited_unmarked with (LeaveNode (v0 :: vs) m :: h1); auto.
      intros; intro.
      apply H0; exists st; auto.
      left; auto.
    } Unfocus.
    exfalso.
    apply H0.
    apply in_chain_visited with (LeaveNode (v0 :: vs) m); simpl; auto.
    inversion H1; subst; auto.
    right; left; auto.
Qed.

Lemma visited_visited_unmarked: forall v h,
  (negateP m_init) v ->
  History h ->
  (exists st, In st h /\ at_node st v) ->
  exists vs m, In (EnterNode (v :: vs) m) h /\ (negateP m) v.
Proof.
  intros.
  induction h as [| st h].
  + inversion H0.
  + destruct (visited_decidable v h).
    - spec IHh; [apply History_cons_rev in H0; destruct H0; [destruct H2 as [? [HH ?]]; subst; inversion HH | auto] |].
      spec IHh; [auto |].
      clear - IHh.
      destruct IHh as [st0 [m [? ?]]]; exists st0, m; simpl; tauto.
    - clear IHh.
      destruct H1 as [st0 [[? | ?] ?]]; [| exfalso; apply H2; eauto].
      subst st0.
      pose proof first_visit_unmarked v st h H H0 H2 H3.
      destruct H1 as [vs [m [? ?]]].
      subst st; exists vs, m.
      split; [left |]; auto.
Qed.

Lemma in_will_leave: forall h vs,
  History h ->
  (exists m vs' m' h1 h2 h3, length vs' <= length vs /\ h = h1 ++ (LeaveNode vs' m') :: h2 ++ (InNode vs m) :: h3) ->
  exists m h1 h3, h = h1 ++ LeaveNode vs m :: InNode vs m :: h3.
Proof.
  intros.
  assert (AUX: forall st1 st2 h,
                (forall m h1 h3, ~ st1 :: st2 :: h = h1 ++ LeaveNode vs m :: InNode vs m :: h3) <->
                (~ exists m, (st1 = LeaveNode vs m /\ st2 = InNode vs m)) /\
                (forall m h1 h3, ~ st2 :: h = h1 ++ LeaveNode vs m :: InNode vs m :: h3)).
  Focus 1. {
    intros.
    split; intros; [split | destruct h1].
    + intros [m [? ?]].
      specialize (H1 m nil h0).
      simpl in H1; congruence.
    + intros.
      specialize (H1 m (st1 :: h1) h3).
      simpl in H1; congruence.
    + destruct H1 as [? _].
      intro; apply H1.
      exists m; inversion H2; auto.
    + destruct H1 as [_ ?].
      specialize (H1 m h1 h3).
      simpl; congruence.
  } Unfocus.
  cut (~ forall m h1 h3, ~ h = h1 ++ LeaveNode vs m :: InNode vs m :: h3).
  Focus 1. {
    intros. clear H0.
    assert (AUX0: forall st1 st2 h,
                   (exists m, st1 = LeaveNode vs m /\ st2 = InNode vs m) \/
                   (exists m h1 h3, st2 :: h = h1 ++ LeaveNode vs m :: InNode vs m :: h3) ->
                   (exists m h1 h3, st1 :: st2 :: h = h1 ++ LeaveNode vs m :: InNode vs m :: h3)).
    Focus 1. {
      intros; destruct H0 as [[m [? ?]] | [m [h1 [h3 ?]]]].
      + exists m, nil, h0; subst; auto.
      + exists m, (st1 :: h1), h3; rewrite H0; auto.
    } Unfocus.
    assert (AUX1: forall st1 st2 h,
                   History (st1 :: st2 :: h) -> 
                   (~ forall m h1 h3, ~ st1 :: st2 :: h = h1 ++ LeaveNode vs m :: InNode vs m :: h3) ->
                   (exists m, (st1 = LeaveNode vs m /\ st2 = InNode vs m)) \/
                   (~ forall m h1 h3, ~ st2 :: h = h1 ++ LeaveNode vs m :: InNode vs m :: h3)).
    Focus 1. {
      intros.
      rewrite AUX in H2.
      apply demorgan_weak'; auto.
      clear - H0.
      remember (st1 :: st2 :: h0); inversion H0; subst;
      try solve
       [match goal with
        | HH0: _ :: _ :: _ = st1 :: st2 :: h0 |- _ =>
           let HH1 := fresh "H" in
           let HH2 := fresh "H" in
           let m0 := fresh "m" in
           inversion HH0; subst;
           right;
           intros [m0 [HH1 HH2]];
           inversion HH1; inversion HH2
        end].
      + inversion H.
      + inversion H2; subst.
        destruct (list_eq_dec t_eq_dec vs (v :: vs0)); [left | right].
        - exists m; subst; auto.
        - intros [m0 [? ?]]; apply n.
          inversion H3; auto.
    } Unfocus.
    induction H;
    try (apply AUX1 in H1; [| constructor; auto];
         apply AUX0;
         destruct H1; [left | right; apply IHHistory]; auto).
    exfalso.
    apply H1.
    intros.
    intro.
    destruct h1; [simpl in H; congruence |].
    destruct h1; simpl in H; congruence.
  } Unfocus.
  intro.
  destruct H0 as [m [vs' [m' [h1 [h2 [h3 [? ?]]]]]]].
  remember (LeaveNode vs' m') as st eqn:?H.
  revert H0; cut (length vs' > length vs); [intros; omega |].
  cut (exists vs_pre0 vs_pre, vs' = vs_pre0 :: vs_pre ++ vs);
    [intros [? [? ?]]; subst; simpl; rewrite app_length; omega |].
  revert vs' m' H3.
  cut ((forall vs' m', st = EnterNode vs' m' -> exists vs_pre0 vs_pre, vs' = vs_pre0 :: vs_pre ++ vs) /\
       (forall vs' m', st = InNode vs' m' -> exists vs_pre, vs' = vs_pre ++ vs) /\
       (forall vs' e' m', st = ForwardEdge vs' e' m' -> exists vs_pre, vs' = vs_pre ++ vs) /\
       (forall vs' m', st = LeaveNode vs' m' -> exists vs_pre0 vs_pre, vs' = vs_pre0 :: vs_pre ++ vs));
    [intro; tauto |].
  revert st h1 h2 h3 H2; induction H; intros;
  try
   (rewrite AUX in H1; destruct H1;
    spec IHHistory; [auto |];
    match goal with
    | HH0 : _ :: _ :: h = _ ++ st :: h2 ++ _ :: h3 |- _ =>
       destruct h1;
       [ inversion HH0;
         match goal with
         | HH1 : _ :: h = h2 ++ _ :: h3 |- _ =>
           split; [| split; [| split]]; try (intros; subst; congruence);
           first [intros ? ? ? HH2 | intros ? ? HH2];
           destruct h2 as [| st' h2];
            [solve [ inversion HH1
                  | inversion HH1; inversion HH2; subst; simpl; eauto
                  | inversion HH1; inversion HH2; subst; simpl; exists nil; auto
                  | inversion HH1; inversion HH2; subst; exfalso; apply H1; eauto] |];
           specialize (IHHistory st' nil h2 h3 HH1);
           inversion HH1;
           match goal with
           | _ : EnterNode _ _ = st' |- _ => destruct IHHistory as [HH3 [_ [_ _]]]
           | _ : InNode _ _ = st' |- _ => destruct IHHistory as [_ [HH3 [_ _]]]
           | _ : ForwardEdge _ _ _ = st' |- _ => destruct IHHistory as [_ [_ [HH3 _]]]
           | _ : LeaveNode _ _ = st' |- _ => destruct IHHistory as [_ [_ [_ HH3]]]
           end;
           inversion HH2; subst;
           first [specialize (HH3 _ _ eq_refl) | specialize (HH3 _ _ _ eq_refl)];
           first [destruct HH3 as [? [? HH3]] | destruct HH3 as [? HH3]]; inversion HH3; subst;
           try solve [repeat rewrite app_comm_cons; eauto | eauto]
         end
       | apply IHHistory with h1 h2 h3;
         inversion HH0; subst; auto]
    end).
  + destruct h1 as [| ? [| ? ?]], h2; try (simpl in H2; congruence).
  + rewrite H5 in *; clear HH3 H5.
    destruct x.
    - exfalso; apply H1.
      simpl; eauto.
    - simpl; eauto.
Qed.

Lemma leave_no_edge_missing: forall h v e,
  History h ->
  src e = v ->
  evalid e ->
  (exists m vs h1 h3, h = h1 ++ LeaveNode (v :: vs) m :: InNode (v :: vs) m :: h3) ->
  (exists m vs, In (ForwardEdge vs e m) h).
Proof.
  intros.
  destruct H2 as [? [? [h1 [h2 ?]]]].
  subst.
  apply partial_History_rev in H.
  destruct H; [congruence |].
  inversion H; subst.
  specialize (H9 _ eq_refl).
  spec H9; [auto |].
  destruct H9 as [st [? ?]].
  destruct st; simpl in H2; try tauto.
  subst.
  exists n, l.
  apply in_app_iff.
  do 3 right.
  auto.
Qed.

Lemma root_visited: forall h, History h -> exists m vs, In (EnterNode (root :: vs) m) h.
Proof.
  intros.
  induction H;
  try (destruct IHHistory as [m0 [vs0 ?]]; exists m0, vs0; right; auto).
  exists m_init, nil.
  left; auto.
Qed.

Variable m_term: Marking.
Variable h_full: list State.
Hypothesis h_full_legal: History h_full.
Hypothesis h_full_terminate: head h_full = Some (LeaveNode (root :: nil) m_term).

Lemma first_visited_been_in: forall v,
  vvalid v ->
  (negateP m_init) v ->
  (exists vs m, In (EnterNode (v :: vs) m) h_full /\ (negateP m) v) ->
  exists vs m, In (InNode (v :: vs) m) h_full.
Proof.
  intros.
  destruct H1 as [vs [m [? ?]]].
  apply in_split in H1.
  destruct H1 as [h1 [h2 ?]].
  destruct (foot h1) eqn: HH; [| apply foot_none_nil in HH; subst h1 h_full; inversion h_full_terminate].
  apply foot_explicit in HH.
  destruct HH as [h1' ?]; subst h1.
  rewrite <- app_cons_assoc in H1.
  subst h_full.
  apply partial_History_rev in h_full_legal.
  destruct h_full_legal; [congruence |].
  inversion H1; subst.
  + exists vs, m'.
    rewrite in_app_iff; right; left; auto.
  + rewrite negateP_spec in H2; tauto.
Qed.

Lemma in_after_forward: forall e,
  (exists m vs, In (ForwardEdge vs e m) h_full) ->
  (exists m vs, In (EnterNode (dst e :: vs) m) h_full).
Proof.
  intros.
  destruct H as [m [vs ?]].
  apply in_split in H.
  destruct H as [h1 [h2 ?]].
  destruct (foot h1) eqn: HH; [| apply foot_none_nil in HH; subst h1 h_full; inversion h_full_terminate].
  apply foot_explicit in HH.
  destruct HH as [h1' ?]; subst h1.
  rewrite <- app_cons_assoc in H.
  subst h_full.
  apply partial_History_rev in h_full_legal.
  destruct h_full_legal; [congruence |].
  inversion H; subst.
  exists m, vs.
  rewrite in_app_iff; right; left; auto.
Qed.

Lemma marked_marked_forall: forall v,
  (exists st, In st h_full /\ (marking_of_state st) v) ->
  m_term v.
Proof.
  intros.
  destruct h_full as [| st h]; [inversion h_full_terminate |].
  inversion h_full_terminate.
  assert (marking_of_state st = m_term) by (subst; reflexivity).
  clear H1 h_full_terminate.
  pose proof h_full_legal; clear h_full_legal.
  remember (st :: h); induction H1.
  + destruct H as [? [? ?]].
    inversion H; [| tauto].
    inversion Heql; subst.
    auto.
  + 

Lemma reachable_visited: forall v,
  (forall v, reachable G root v -> (negateP m_init) v) ->
  reachable G root v ->
  (exists m vs, In (EnterNode (v :: vs) m) h_full).
Proof.
  intros.
  rewrite reachable_ind2_reachable in H0.
  assert (forall v : V, ind2.reachable G root v -> (negateP m_init) v) by (intro; rewrite <- reachable_ind2_reachable; auto); clear H.
  remember root eqn: HH; revert HH; induction H0; intros; subst.
  + apply root_visited; auto.
  + do 3 (spec IHreachable; [auto |]).
    assert (exists st, In st h_full /\ at_node st y).
    Focus 1. {
      destruct IHreachable as [m [vs ?]].
      exists (EnterNode (y :: vs) m).
      split; auto.
      constructor.
    } Unfocus.
    clear IHreachable.
    apply visited_visited_unmarked in H2; [| auto | auto].
    apply first_visited_been_in in H2; [| destruct H; tauto | auto].
    destruct H2 as [vs ?].
    assert (exists m vs' m' h1 h2 h3,
              length vs' <= length (y :: vs) /\
              h_full = h1 ++ LeaveNode vs' m' :: h2 ++ InNode (y :: vs) m :: h3).
    Focus 1. {
      destruct H2 as [m ?]; exists m.
      apply in_split in H2.
      destruct H2 as [h2 [h3 ?]].
      destruct h2.
      + subst; inversion h_full_terminate.
      + subst; inversion h_full_terminate.
        subst s.
        exists (root :: nil), m_term, nil, h2, h3.
        split; auto.
        simpl; omega.
    } Unfocus.
    clear H2.
    apply in_will_leave in H3; [| auto].
    assert (exists m vs h1 h3, h_full = h1 ++ LeaveNode (y :: vs) m :: InNode (y :: vs) m :: h3).
    Focus 1. {
      destruct H3 as [m ?].
      exists m, vs; auto.
    } Unfocus.
    clear H3 vs.
    destruct H as [? [? ?]].
    rewrite step_spec in H4.
    destruct H4 as [e [? [? ?]]].
    apply (leave_no_edge_missing _ _ _ h_full_legal H5 H4) in H2.
    apply in_after_forward in H2.
    rewrite H6 in H2.
    auto.
Qed.