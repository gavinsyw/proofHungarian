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

Arguments PreGraph _ _ {_} {_}.

Section BiGraph.
Definition V:=nat.
Context {E : Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.

(* 
Record PreGraph (Vertex Edge : Type) (EV : EqDec Vertex eq)
(EE : EqDec Edge eq) : Type := Build_PreGraph
  { vvalid : Ensemble Vertex;
    evalid : Ensemble Edge;
    src : Edge -> Vertex;
    dst : Edge -> Vertex }

Record LabeledGraph (Vertex Edge : Type) (EV : EqDec Vertex eq)
(EE : EqDec Edge eq) (DV DE DG : Type) : Type
  := Build_LabeledGraph
  { pg_lg : PreGraph Vertex Edge;
    vlabel : Vertex -> DV;
    elabel : Edge -> DE;
    glabel : DG }

    *)


Definition BiGraph_re (pg: PreGraph V E) (f : V -> bool ): Prop :=
  forall e x y, evalid pg e -> src pg e = x -> dst pg e = y -> f x = negb (f y).

Record BiGraph := {
 bgraph : PreGraph V E ;
 vlabel : V -> bool ; (* 表示两个点集 *)
 re : BiGraph_re bgraph vlabel
}.




Definition Vstate:= V -> Prop.
Definition default_Vstate : Vstate := (fun _ => False).
Definition Vstate_update (m : Vstate) (v: V) : Vstate :=
 fun x =>   x =  v \/ m x.
Definition Vstate_updata_f (m : Vstate) (v: V) : Vstate :=
 fun x =>  ( x = v -> False ) \/ (~ x = v  -> m x).

Definition Vstate_update_l (m : Vstate) (v : list V) : Vstate :=
 fun x => In x v \/ m x.

Definition Vstate_update_fl (m : Vstate) (v : list V) : Vstate :=
 fun x => (In x v -> False ) \/ (~ In  x  v  -> m x).

Definition matching := list E.
Context {BG : BiGraph }.



Fixpoint list_sub (u v :list V) : list V :=
match v with 
|nil => u
|e::v' => list_sub (remove EV e u ) v'
end.
Notation Gph := (PreGraph V E).

Fixpoint epath_to_vpath (g: Gph) (p : list E) {struct p} : list V :=
  match p with
  | nil => nil
  | e :: nil => dst g e :: src g e :: nil
  | e :: el => dst g e :: epath_to_vpath' g el
  end.

(*均为有向*)
Definition gra := bgraph BG.

Definition e_to_v (p : list E) : list V := epath_to_vpath gra p .
Fixpoint Ma (v : V) (M :matching): (option V) := 
match M with 
|nil => None
|e::m' => if Nat.eqb (src gra e) v then 
          Some (dst gra e) else 
            (Ma v m')
end.


Context {M : matching}.

Definition Matching (v: V) : (option V) := Ma v M.
Definition path : Type := (V * list E)%type.


(* Definition crossGraph (matching) : Type :=  PreGraph 

 *)

Print Nat.odd.

Inductive cross_step : (Vstate * path) -> (Vstate * path ) -> Prop := 
| one_v : forall (u v w: V ) (e1 e2 : E) (v1 : Vstate) , v1 = Vstate_update default_Vstate u  -> 
    Matching u  = None ->
    src gra e1 = u -> dst gra e1 = v  ->src gra e2 = v -> dst gra e2 = w -> In e2 M ->(*->
      Matching v = Some w -> *)
         cross_step (v1, (u, nil)) ( Vstate_update (Vstate_update v1  v) w  , (w ,e2 :: (e1::nil)))
(**从一个非匹配点 经过非匹配边和匹配边  到一个匹配点 *)
| not_one : forall (u v w: V ) (e1 e2 e3 : E)(p :list E) (v1: Vstate), (* ???  *) 
    dst gra e3 = u -> In e3 M -> (* Nat.odd (length p) = true ->*)
    v1 u -> ~ v1 v -> ~ v1 w ->
    src gra e1 = u -> dst gra e1 = v  -> src gra e2 = v -> dst gra e2 = w -> In e2 M ->(*->
      Matching v = Some w -> *)
         cross_step (v1, (u, e3 :: p)) ( Vstate_update (Vstate_update v1  v) w  , (w ,e2::(e1::(e3::p))))
(**从一个匹配点 经过非匹配边和匹配边  到一个匹配点 *)
|no_to_no : forall (u v : V ) (e : E) (p: list E)  (v1 : Vstate) ,
   v1 u -> ~ v1 v ->
   src gra e = u -> dst gra e = v  ->
         cross_step (v1, (u, p)) ( Vstate_update v1  v , (v ,e::p))
(**从一个非匹配点到非匹配点*)
|turn_back: forall(u v w: V)(e1 e2 e3 :E)(p: list E) (q:list V)(v1: Vstate),
    dst gra e3 = u -> In e3 M ->
    v1 u -> v1 v -> v1 w ->
    src gra e1 = u -> dst gra e1 = v  -> src gra e2 = v -> dst gra e2 = w -> In e2 M -> 
      cross_step (v1, (w, e2::(e1::(e3::p)))) (Vstate_update_fl (Vstate_updata_f v1 w) q, (u, e3::p)).
(**回溯 从一个匹配点回溯到 一个匹配点*)

(*
Inductive cross_step_halt : (Vstate * path) -> Prop := 
| BTrue: 
*)

Definition AugmentPath := Type.

Definition multi_step := Type.

(* If there is a maximum matching, there will be no augment path on the graph
   If there is an augment path, there will always be a bigger matching.*)
(* 
Inductive matching (pg: PreGraph V E): Ensemble V -> list E -> Prop :=
  | emptyMatch : matching pg (Empty_set V) nil
  | normalMatch: forall (v: Ensemble V) (p: list E) (e: E), 
    matching pg v p -> strong_evalid pg e -> ~Ensembles.In _ v (src pg e) -> 
    ~Ensembles.In _ v (dst pg e) -> 
    matching pg (Ensembles.Add V (Ensembles.Add V v (src pg e)) (dst pg e)) (e::p).

Print path.

Print negb.
Print Bool.eqb.
Print cons.
Print hd.
Definition path : Type := (V * list E)%type.
Print LabeledGraph.

Notation Graph := (@LabeledGraph V E EV EE bool bool GraphType).

Local Coercion pg_lg: LabeledGraph >-> PreGraph.





Print elabel.

Inductive cross_step (g: Graph): path -> path -> Prop :=
  | CRS_Empty: forall (v: V) (e: E) (p: path), fst p = v -> snd p = nil
    -> strong_evalid g e -> valid_path g (v, e::nil)
    -> cross_step g p (v, e::nil)
  | CRS_Match: forall (v ev: V) (e e': E) (le: list E) (p: path), fst p = v -> snd p = le
    -> strong_evalid g e -> e' = hd e le -> negb (elabel g e) = (elabel g e')
    -> src g e = ev -> valid_path g (ev, e::le) -> cross_step g p (ev, e::le).
(* Inductive cross_step (pg: PreGraph V E): path -> path -> Prop :=
  | CRS_Empty: forall (v: V) (e: E) (p: path), fst p = v -> snd p = nil -> strong_evalid pg e -> valid_path pg (v, e::nil)
    -> cross_step pg p (v, e::nil)
  | CRS_Match: forall (v: V) (
  | CRS_Match: forall (v: V) (le: list E) (e: E) (p:path), fst p = v -> snd p = le -> strong_evalid pg e ->
     matching pg le -> ~matching pg e -> cross_step pg p (v, le::e). 
  | CRS_Single: forall (v:V) (e:E), evalid pg e -> valid_path pg (v, e::nil) -> 
    cross_step . *)
  
 *)