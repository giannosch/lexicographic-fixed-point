Require Import BasicLogic.
Require Import Sets.
Require Import Order.
Require Import Functions.
Require Import Ordinal.

Lemma Prelattice_definition {L:Set} (leq: L->L->Prop) (S:Pow L):
  Preorder leq ->
  (exists b, Bottom leq b S) ->
  (forall X:Pow L, X ⊆ S->X<>Empty_set L->(exists x, x ∈ S /\ LeastUpperBound leq S x X)) ->
  CompletePrelattice leq S.
Proof.
  intros.
  apply Build_CompletePrelattice;intros.
  exact H.
  (* LUB *)
    pose (LEM (X=Empty_set L)).
    (* X is empty *)
      destruct o.
      destruct H0 as [b].
      exists b.
      split.
      (* b in S *)
        destruct H0.
        exact H0.
        split.
      (* UpperBound leq b X *)
        unfold UpperBound.
        unfold Forall_left.
        intros.
        rewrite H3 in H4.
        unfold In in H4.
        induction H4.
      (* Least of Upper bounds *)
        intros.
        destruct H0.
        exact (H6 y H4).
    (* X is not empty *)
      apply (H1 X H2 H3).
  (* GLB *)
    pose (LB := S ∩ (fun s => LowerBound leq s X)).
    assert (LB<>Empty_set L).
      destruct H0 as [b].
      apply (Has_something_then_not_empty b).
      unfold In.
      unfold LB.
      destruct H0.
      split.
      exact H0.
      unfold In.
      exact (LowerBound_subset H3 H2).
    destruct (H1 LB (Intersection_subset S (fun s => LowerBound leq s X)) H3) as [y].
    exists y.
    destruct H4.
    split.
    exact H4.
    split.
    (* LowerBound *)
      unfold LowerBound.
      unfold Forall_right.
      intro x; intros.
      destruct H5.
      apply (H7 x (H2 x H6)).
      unfold UpperBound.
      unfold Forall_left.
      intros.
      unfold LB in H8.
      unfold In in H8.
      destruct H8.
      exact (H9 x H6).
    (* Greatest of UpperBounds *)
      intro z.
      intros.
      destruct H5.
      apply H5.
      split.
      exact H6.
      exact H7.
Qed.


Lemma Subprelattice {L:Set} {leq:L->L->Prop} {S:Pow L} {v:L}:
  v ∈ S -> CompletePrelattice leq S -> CompletePrelattice leq (S ∩ (fun x => leq v x)).
Proof.
  pose (Intersection_subset S (fun x => leq v x)).
  intros.
  destruct H0.
  apply Prelattice_definition.
  exact cpl_preorder.
  (* Bottom *)
    exists v.
    split.
    unfold In.
    split.
    exact H.
    unfold In.
    reflexivity.
    unfold LowerBound.
    unfold Forall_right.
    intros.
    destruct H0.
    exact H1.
  (* LUB *)
    intros.
    destruct (cpl_lub X (Included_transitivity (S ∩ (fun x : L => leq v x)) H0 i)) as [y].
    destruct H2.
    destruct H3.
    exists y.
    split.
    (* y in S cap (fun x : L => leq v x) *)
      unfold In.
      split.
      exact H2.
      destruct (Not_empty_then_has_something H1) as [x].
      unfold In.
      transitivity (x).
      destruct (H0 x H5).
      exact H7.
      exact (H3 x H5).
    (* Least Upper Bound *)
      split.
      exact H3.
      intros.
      apply (H4 y0 (i y0 H5) H6).
Qed.

Lemma Subprelattice_compatible {L:Set} (leq:L->L->Prop) (S:Pow L) (f:L->L) (v:L):
  v ∈ S -> 
  leq v (f v) ->
  Preorder leq -> 
  Monotonic leq f-> 
  Compatible f S -> 
  Compatible f (fun x => x ∈ S /\ leq v x).
Proof.
  intros.
  unfold Compatible.
  unfold In.
  intros.
  destruct H4.
  split.
  exact (H3 x H4).
  transitivity (f v).
  exact H0.
  exact (H2 v x H5).
Qed.

Lemma Knaster_tarski {L:Set} {leq:L->L->Prop} {S:Pow L} {f:L->L}:
  CompletePrelattice leq S ->
  Compatible f S ->
  Monotonic leq f ->
  exists x, x ∈ S /\ leq x (f x) /\ leq (f x) x /\
    forall y, y ∈ S -> leq (f y) y -> leq x y.
Proof.
  intros.
  pose (P := S ∩ (fun x => leq (f x) x)).
  destruct (cpl_glb P (Intersection_subset S (fun x => leq (f x) x))) as [x].
  exists x.
  destruct H2.
  destruct H3.
  split.
  (* x in S *)
    exact H2.
  (* Prove Goal 2 first *)
  assert (leq (f x) x).
    assert (LowerBound leq (f x) P).
      unfold LowerBound.
      unfold Forall_right.
      intros.
      transitivity (f y).
      apply H1.
      exact (H3 y H5).
      unfold P in H5.
      destruct H5.
      exact H6.
    apply (H4 (f x) (H0 x H2) H5).
  split.
  (* leq x (f x) *)
    apply H1 in H5.
    apply H3.
    unfold P.
    unfold In.
    split.
    exact (H0 x H2).
    exact H5.
  split.
  (* leq (f x) x *)
    exact H5.
  (* least prefixed *)
    intros.
    apply H3.
    unfold P.
    unfold In.
    split.
    exact H6.
    exact H7.
Qed.


Parameter L: Set.
Parameter Sqleq: L->L->Prop.
Parameter Sqleqa: Ord->L->L->Prop.
Parameter k: Ord.

Notation "(⊑)" := Sqleq.
Notation "x '⊑' y" := (Sqleq x y) (at level 70).
Notation "x '⊏' y" := (Strict Sqleq x y) (at level 70).
Notation "⊑( a )" := (Sqleqa a) (at level 50).
Notation "x '⊑(' a ')' y" := (Sqleqa a x y) (at level 70).
Notation "x '⊏(' a ')' y" := (Strict (Sqleqa a) x y) (at level 70).
Notation "x '=(' a ')' y" := (Equiv (Sqleqa a) x y) (at level 70).
Notation "≈( a )" := (Approx (fun b => Equiv (Sqleqa b)) a) (at level 50).
Notation "x '≈(' a ')' y" := (Approx (fun b => Equiv (Sqleqa b)) a x y) (at level 70).
Notation "'[' x ']' a" := (Equiv_class (Equiv (Sqleqa a)) x) (at level 30).
(* Notation "'(' x ']' a" := (Equiv_class (Equiv (Approx (fun b : Ord => Equiv (Sqleqa b)) a)) x) (at level 30). *)

Section  LexicographicLattices.

Context `{!LexicographicLattice Sqleq k Sqleqa}.

Lemma Sqsubset_circ_sqsubseteq {a:Ord} {x y z:L}:
  a<k -> x ⊏(a) y -> y ⊑(a) z -> x ⊏(a) z.
Proof.
  intros.
  destruct H0.
  pose (ll_preorders a H).
  split.
  (* x ⊑( a) z *)
    transitivity (y); assumption.
  (* ~ z ⊑( a) x *)
    unfold not.
    intros.
    destruct p.
    case (H2 (preorder_transitive y z x H1 H3)).
Qed.

Lemma Sqsubseteq_circ_sqsubset {a:Ord} {x y z:L}:
  a<k -> x ⊑(a) y -> y ⊏(a) z -> x ⊏(a) z.
Proof.
  intros.
  destruct H1.
  pose (ll_preorders a H).
  split.
  (* x ⊑( a) z *)
    transitivity (y); assumption.
  (* ~ z ⊑( a) x *)
    unfold not.
    intros.
    destruct p.
    case (H2 (preorder_transitive z x y H3 H0)).
Qed.

Lemma Aux_Sqleq_definition {x y:L}:
  x ⊑ y -> x=y \/ x⊏y.
Proof.
  intros.
  destruct (LEM (x=y)).
  exact (or_introl H0).
  apply or_intror.
  unfold Strict.
  split.
  exact H.
  unfold not.
  intro.
  case (H0 (antisymmetry H H1)).
Qed.

Lemma Aux_Sqleqa_definition {a:Ord} {x y:L}:
  x ⊑(a) y -> x=(a)y \/ x⊏(a)y.
Proof.
  intros.
  destruct (LEM (x=(a)y)).
  exact (or_introl H0).
  apply or_intror.
  unfold Strict.
  split.
  exact H.
  unfold not.
  intro.
  unfold Equiv in H0.
  assert (x ⊑( a) y /\ y ⊑( a) x).
    split;assumption.
  case (H0 H2).
Qed.

Lemma Alpha {a:Ord} {x y:L}:
  a<k -> x ⊑ y -> x ≈(a) y -> x ⊑(a) y.
Proof.
  intros.
  pose (ll_preorders a H).
  apply Aux_Sqleq_definition in H0.
  destruct H0.
  (* x = y *)
    rewrite H0.
    reflexivity.
  (* x ⊏ y *)
    apply (sqlt_determined1 x y) in H0.
    destruct H0 as [b].
    destruct H0.
    destruct (Ord_lt_total b a).
    (* b<a *)
      unfold Approx in H1.
      pose (H1 b H3).
      unfold Equiv in e.
      destruct e.
      unfold Strict in H2.
      destruct H2.
      case (H6 H5).
    destruct H3.
    (* a=b *)
      destruct H2.
      rewrite <- H3.
      exact H2.
    (* a<b *)
      destruct H2.
      pose (property1 b x y H0 H2).
      unfold Approx in a0.
      destruct (a0 a H3).
      exact H5.
Qed.

Lemma Aux_Equiv_a_approx_succ_a {a:Ord} {x y:L}: 
  a<k -> x =(a) y -> x ≈(Succ a) y.
Proof.
  intros.
  destruct H0.
  pose (property1 a x y H H0).
  unfold Approx.
  intros.
  destruct (Ord_lt_succ H2).
  exact (a0 b H3).
  split;rewrite H3;assumption.
Qed.

Lemma Aux_Approx_succ_a_equiv_a {a:Ord} {x y:L}: 
  a<k -> x ≈(Succ a) y -> x =(a) y.
Proof.
  intros.
  pose (Ord_succ_gt a).
  exact (H0 a o).
Qed.

Lemma Aux_Approx_a_approx_lt_a {a b:Ord} {x y:L}:
  b<a ->x ≈(a) y -> x ≈(b) y.
Proof.
  unfold Approx.
  intros.
  exact (H0 b0 (Ord_lt_transitivity H1 H)).
Qed.

Lemma Aux_Approx_symmetric {a: Ord} {x y: L}:
  x ≈(a) y -> y ≈(a) x.
Proof.
  unfold Approx.
  intros.
  destruct (H b H0).
  split;assumption.
Qed.

Lemma Aux_Approx_transitive {a: Ord} (x y z: L): 
a<k -> x ≈(a) y -> y ≈(a) z -> x ≈(a) z.
Proof.
  unfold Approx.
  intros.
  destruct (H0 b H2).
  destruct (H1 b H2).
  pose (ll_preorders b (Ord_lt_transitivity H2 H)).
  split; transitivity (y);assumption.
Qed.

Lemma Aux_Equiv_symmetric {a: Ord} {x y: L}:
  x =(a) y -> y =(a) x.
Proof.
  unfold Equiv.
  intros.
  destruct H.
  split;assumption.
Qed.

Definition Closed (r:L->L->Prop) (X:Pow L) := forall x y, x∈X -> y∈X -> r x y.

Lemma Closed_lub {a:Ord} {X:Pow L} {x:L}:
  a<k -> X<>Empty_set L-> X FA_l(≈(a)) x -> (lub X) ≈(a) x.
Proof.
  intros.
  rename H0 into H11.
  destruct (Not_empty_then_has_something H11) as [x'].
  apply (Aux_Approx_transitive (lub X) x' x H).
  (* lub X ≈( a) x' *)
    pose (fcl_lub X).
    destruct l.
    pose (H2 x' H0).
    apply Aux_Sqleq_definition in s.
    destruct s.
    (* y = lub X *)
      unfold Approx.
      intros.
      unfold Equiv.
      pose (ll_preorders b (Ord_lt_transitivity H5 H)).
      split;rewrite H4;reflexivity.
    (* y ⊏ lub X *)
      apply sqlt_determined1 in H4.
      destruct H4 as [b].
      destruct H4.
      destruct (Ord_lt_total b a).
      (* b<a *)
        pose (y:= lub ([x']b)).
        assert (X ⊆ ([x']b)).
          unfold Included.
          intros.
          unfold Equiv_class.
          unfold In.
          pose (H1 x0 H7).
          pose (H1 x' H0).
          exact (Aux_Approx_transitive x' x x0 H a1 (Aux_Approx_symmetric a0) b H6).
        destruct (fcl_lub ([x']b)).
        pose (UpperBound_subset H8 H7).
        pose (H3 (lub ([x'] b)) (full_intro L (lub ([x'] b))) u).
        pose (property3_lub x' b).
        destruct e.
        pose (Sqsubseteq_circ_sqsubset H4 H10 H5).
        destruct (sqlt_determined2 y (lub X) b H4 s0).
        case (H14 s).
      destruct H6;destruct H5.
      (* b=a *)
        rewrite H6 in H5.
        exact (Aux_Approx_symmetric (property1 a x' (lub X) H H5)).
      (* a≤b *)
        pose (property1 b x' (lub X) H4 H5).
        exact (Aux_Approx_symmetric (Aux_Approx_a_approx_lt_a H6 a0)).
  (* x' ≈( a) x *)
    exact (H1 x' H0).
Qed.

Lemma Closed_glb {a:Ord} {X:Pow L} {x:L}:
  a<k -> X<>Empty_set L-> X FA_l(≈(a)) x -> (glb X) ≈(a) x.
Proof.
  intros.
  rename H0 into H11.
  destruct (Not_empty_then_has_something H11) as [x'].
  apply (Aux_Approx_transitive (glb X) x' x H).
  (* lub X ≈( a) x' *)
    pose (fcl_glb X).
    destruct g.
    pose (H2 x' H0).
    apply Aux_Sqleq_definition in s.
    destruct s.
    (* y = lub X *)
      unfold Approx.
      intros.
      unfold Equiv.
      pose (ll_preorders b (Ord_lt_transitivity H5 H)).
      split;rewrite H4;reflexivity.
    (* y ⊏ lub X *)
      apply sqlt_determined1 in H4.
      destruct H4 as [b].
      destruct H4.
      destruct (Ord_lt_total b a).
      (* b<a *)
        pose (y:= glb ([x']b)).
        assert (X ⊆ ([x']b)).
          unfold Included.
          intros.
          unfold Equiv_class.
          unfold In.
          pose (H1 x0 H7).
          pose (H1 x' H0).
          exact (Aux_Approx_transitive x' x x0 H a1 (Aux_Approx_symmetric a0) b H6).
        destruct (fcl_glb ([x']b)).
        pose (LowerBound_subset H8 H7).
        pose (H3 (glb ([x'] b)) (full_intro L (glb ([x'] b))) l).
        pose (property3_glb x' b).
        destruct e.
        pose (Sqsubset_circ_sqsubseteq H4 H5 H12).
        destruct (sqlt_determined2 (glb X) y b H4 s0).
        case (H14 s).
      destruct H6;destruct H5.
      (* b=a *)
        rewrite H6 in H5.
        exact (property1 a (glb X) x' H H5).
      (* a≤b *)
        pose (property1 b (glb X) x' H4 H5).
        exact (Aux_Approx_a_approx_lt_a H6 a0).
  (* x' ≈( a) x *)
    exact (H1 x' H0).
Qed.

Lemma Lub_a_bound {a:Ord} {X:Pow L}:
  a<k -> Closed (≈(a)) X -> X FA_l(⊑(a)) (lub X).
Proof.
  unfold Forall_left.
  intros.
  assert (X FA_l(≈(a)) x).
    unfold Forall_left.
    intros.
    exact (H0 x0 x H2 H1).
  pose (Closed_lub H (Has_something_then_not_empty x H1) H2).
  destruct (fcl_lub X).
  exact (Alpha H (H3 x H1) (Aux_Approx_symmetric a0)).
Qed.

Lemma Glb_a_bound {a:Ord} {X:Pow L}:
  a<k -> Closed (≈(a)) X -> (glb X) FA_r(⊑(a)) X.
Proof.
  unfold Forall_right.
  intros.
  assert (X FA_l(≈(a)) y).
    unfold Forall_left.
    intros.
    exact (H0 x y H2 H1).
  pose (Closed_glb H (Has_something_then_not_empty y H1) H2).
  destruct (fcl_glb X).
  exact (Alpha H (H3 y H1) a0).
Qed.

Lemma Aux_Interval_definition {a:Ord} {x y:L}:
  y =(a) x -> y∈[x]a.
Proof.
  unfold Equiv_class.
  intros.
  unfold In.
  exact (Aux_Equiv_symmetric H).
Qed.

Lemma Aux_X_in_class_x {a:Ord} {x:L}:
  a<k -> x∈[x]a.
Proof.
  intro.
  unfold Equiv_class.
  unfold In.
  pose (ll_preorders a H).
  split; reflexivity.
Qed.

Lemma Lub_a_least_upper_bound {a:Ord} {X:Pow L} {x:L}:
  a<k -> X<>Empty_set L -> Closed (≈(a)) X -> X FA_l(⊑(a)) x -> lub X ⊑(a) x.
Proof.
  intros.
  pose (y:=lub ([x]a)).
  assert (UpperBound (⊑) y X).
    unfold UpperBound.
    unfold Forall_left.
    intros.
    destruct (fcl_lub ([x]a)).
    destruct (LEM (x0 =(a) x)).
      (* x0 =( a) x *)
        exact (H4 x0 (Aux_Interval_definition H6)).
      (* ~ x0 =( a) x *)
        transitivity (x).
        (* x0 ⊑ x *)
          apply H2 in H3.
          apply (Aux_Sqleqa_definition) in H3.
          destruct H3.
          case (H6 H3).
          destruct (sqlt_determined2 x0 x a H H3).
          exact H7.
        (* x ⊑ y *)
          exact (H4 x (Aux_X_in_class_x H)).
  destruct (fcl_lub X).
  pose (H5 y (full_intro L y) H3).
  assert (lub X ≈(a) y).
    assert (X FA_l(≈(a)) x).
      unfold Forall_left.
      intros.
      exact (property1 a x0 x H (H2 x0 H6)).
    apply (Aux_Approx_transitive (lub X) x y H).
    (* lub X ≈( a) x *)
      exact (Closed_lub H H0 H6).
    (* x ≈( a) y *)
      pose (Aux_Equiv_symmetric (property3_lub x a)).
      exact (Aux_Approx_a_approx_lt_a (Ord_succ_gt a) (Aux_Equiv_a_approx_succ_a H e)).
  pose (Alpha H s H6).
  pose (ll_preorders a H).
  transitivity (y).
  exact s0.
  destruct (property3_lub x a).
  exact H7.
Qed.

Lemma Cap_closed {a:Ord} (X: Ord->Pow L):
  a≤k->Limit a->(forall b, b<a->Closed (≈(b)) (X b))->Closed (≈(a)) (OrdIntersection a X).
Proof.
  intros.
  unfold Closed.
  unfold Approx.
  intros.
  pose (Ord_lt_limit H0 H4).
  induction H2.
  pose (H2 (Succ b) o).
  induction H3.
  pose (H3 (Succ b) o).
  pose (H1 (Succ b) o x x0 i i0).
  refine (Aux_Approx_succ_a_equiv_a _ a0).
  destruct H.
  exact (Ord_lt_transitivity H4 H).
  rewrite <- H.
  exact H4.
Qed.

Definition Complete (X:Pow L) := X<>(Empty_set L) /\
  forall Y, Y<>(Empty_set L)->Y⊆X->lub Y∈X /\ glb Y∈X.

Lemma Class_complete {a:Ord} {X:Pow L} {x:L}:
  a<k->x∈X->Complete X->Complete (X∩[x]a).
Proof.
  unfold Complete.
  intros.
  split.
  (* X ∩ [x] a <> Empty_set *)
    apply (Has_something_then_not_empty x).
    apply intersection_intro.
    exact H0.
    exact (Aux_X_in_class_x H).
  intros.
  assert (Closed (≈(Succ a)) Y).
    unfold Closed.
    intros.
    pose (Intersection_subset ([x]a) X).
    pose (H3 x0 H4).
    pose (H3 y H5).
    rewrite (Intersection_commutative X ([x]a)) in i0.
    rewrite (Intersection_commutative X ([x]a)) in i1.
    pose (Intersection_subset ([x]a) X x0 i0).
    pose (Intersection_subset ([x]a) X y i1).
    apply (Aux_Equiv_a_approx_succ_a H) in i2.
    apply (Aux_Equiv_a_approx_succ_a H) in i3.
    apply (Aux_Approx_symmetric) in i2.
    apply (Aux_Approx_transitive x0 x y (Ord_lt_limit k_limit H));
    assumption.
  destruct H1.
  pose proof H3.
  pose (Included_transitivity (X∩[x]a) H3 (Intersection_subset X ([x]a))).
  rewrite (Intersection_commutative X ([x]a)) in H6.
  pose (Included_transitivity ([x]a∩X) H6 (Intersection_subset ([x]a) X)).
  assert (Y FA_l(≈(Succ a)) x).
      unfold Forall_left.
      intros.
      exact (Aux_Approx_symmetric (Aux_Equiv_a_approx_succ_a H (i0 x0 H7))).
  split.
  apply intersection_intro.
  (* lub Y ∈ X *)
    destruct (H5 Y H2 i).
    exact H8.
  (* lub Y ∈ [x] a *)
    apply (Aux_Approx_succ_a_equiv_a H).
    exact (Aux_Approx_symmetric (Closed_lub (Ord_lt_limit k_limit H) H2 H7)).
  apply intersection_intro.
  (* glb Y ∈ X *)
    destruct (H5 Y H2 i).
    exact H9.
  (* glb Y ∈ [x] a *)
    apply (Aux_Approx_succ_a_equiv_a H).
    exact (Aux_Approx_symmetric (Closed_glb (Ord_lt_limit k_limit H) H2 H7)).
Qed.

Lemma Complete_and_closed_prelattice {a:Ord} {X:Pow L}:
  a<k -> Complete X -> Closed (≈(a)) X -> CompletePrelattice (⊑(a)) X.
Proof.
  intros.
  destruct H0.
  apply Prelattice_definition.
  exact (ll_preorders a H).
  (* bottom *)
    exists (glb X).
    split.
    (* glb X ∈ X *)
      destruct (H2 X H0 Included_reflexivity).
      exact H4.
    (* LowerBound (⊑( a)) (glb X) X *)
      exact (Glb_a_bound H H1).
  (* subset lub *)
    intros.
    rename X0 into Y.
    exists (lub Y).
    split.
    (* lub Y ∈ X *)
      destruct (H2 Y H4 H3).
      exact H5.
    assert (Closed (≈(a)) Y).
      unfold Closed.
      intros.
      exact (H1 x y (H3 x H5) (H3 y H6)).
    split.
    (* Upper bound *)
      exact (Lub_a_bound H H5).
    (* Least of upper bounds *)
      intros.
      exact (Lub_a_least_upper_bound H H4 H5 H7).
Qed.

Lemma Cap_not_empty {a:Ord} (X: Ord->Pow L):
  a≤k -> Limit a ->
  (forall b, b<a -> Complete (X b)) -> 
  (forall b c, b<c->c<a -> X c ⊆ X b) ->
  OrdIntersection a X<>Empty_set L.
Proof.
  intros.
  pose (x_:= fun b => glb (X b)).
  pose (x:= lub (fun y => exists b, b<a /\ x_ b = y)).
  assert (forall b c, b<c -> c<a -> x_ b ⊑ x_ c).
    intros.
    destruct (fcl_glb (X b)).
    apply H5.
    apply (H2 b c H3 H4).
    destruct (H1 c H4).
    destruct (H8 (X c) H7 (Included_reflexivity)).
    exact H10.
  pose (x':=fun b=> lub(fun y => exists c, b<c /\ c<a /\ x_ c = y)).
  assert (forall b, b<a -> x = x' b).
    intros.
    apply antisymmetry.
    (* x ⊑ x' b *)
      destruct (fcl_lub (fun y => exists b, b<a /\ x_ b = y)).
      apply (H6 (x' b) (full_intro L (x' b))).
      unfold UpperBound.
      unfold Forall_left.
      intros.
      unfold In in H7.
      destruct H7 as [c].
      destruct H7.
      rewrite <- H8.
      destruct (Ord_leq_total_r c (Succ b)). (* TODO total_l c b*)
      (* c < Succ b *)
        transitivity (x_ (Succ b)).
        exact (H3 c (Succ b) H9 (Ord_lt_limit H0 H4)).
        destruct (fcl_lub (fun y => exists c, b<c /\ c<a /\ x_ c = y)).
        apply H10.
        unfold In.
        exists (Succ b).
        split.
        exact (Ord_succ_gt b).
        split.
        exact (Ord_lt_limit H0 H4).
        reflexivity.
      (* Succ b ≤ c *)
        assert (x_ c ∈ (fun y => exists c, b<c /\ c<a /\ x_ c = y)).
          unfold In.
          exists c.
          split.
          destruct H9.
          exact (Ord_lt_transitivity (Ord_succ_gt b) H9).
          rewrite <- H9.
          exact (Ord_succ_gt b).
          split.
          exact H7.
          reflexivity.
        destruct (fcl_lub (fun y => exists c, b<c /\ c<a /\ x_ c = y)).
        exact (H11 (x_ c) H10).
    (* x' b ⊑ x *)
    assert ((fun y => exists c, b<c /\ c<a /\ x_ c = y) ⊆ (fun y => exists b, b<a /\ x_ b = y)).
      unfold Included.
      unfold In.
      intros.
      destruct H5 as [c].
      exists c.
      destruct H5.
      exact H6.
    destruct (fcl_lub (fun y => exists c, b<c /\ c<a /\ x_ c = y)).
    apply (H7 x (full_intro L x)).
    destruct (fcl_lub (fun y => exists b, b<a /\ x_ b = y)).
    exact (UpperBound_subset H8 H5).
  apply (Has_something_then_not_empty x).
  apply ord_intersection_intro.
  intros.
  rewrite (H4 b H5).
  apply (H1 b H5).
  (* {x_c:b<c<a}<>Empty_set *)
    apply (Has_something_then_not_empty (x_ (Succ b))).
    unfold In.
    exists (Succ b).
    split.
    exact (Ord_succ_gt b).
    split.
    exact (Ord_lt_limit H0 H5).
    reflexivity.
  (* {x_c:b<c<a}⊆ X b *)
    unfold Included.
    intros.
    unfold In in H6.
    destruct H6 as [c].
    destruct H6.
    destruct H7.
    rewrite <- H8.
    apply (H2 b c H6 H7).
    destruct (H1 c H7).
    destruct (H10 (X c) H9 (Included_reflexivity)).
    exact H12.
Qed.

Lemma Cap_complete {a:Ord} (X: Ord->Pow L):
  a≤k -> Limit a ->
  (forall b, b<a -> Complete (X b)) -> 
  OrdIntersection a X<>Empty_set L ->
  Complete (OrdIntersection a X).
Proof.
  intros.
  split.
  exact H2.
  intros.
  assert (forall b, b<a->Y⊆X b).
    unfold Included.
    intros.
    pose (H4 x H6).
    induction i.
    exact (H7 b H5).
  split;
    apply ord_intersection_intro;
    intros;
    destruct (H1 b H6);
    destruct (H8 Y H3 (H5 b H6));
    assumption.
Qed.

Lemma Cap_compatible {a:Ord} {f:L->L} (X: Ord->Pow L):
  a≤k -> (forall b, b<a -> Compatible f (X b)) -> 
  Compatible f (OrdIntersection a X).
Proof.
  unfold Compatible.
  intros.
  apply ord_intersection_intro.
  intros.
  induction H1.
  exact (H0 b H2 x (H1 b H2)).
Qed.

Definition Stratified_monotonic (f:L->L) := forall a, a<k -> Monotonic (⊑(a)) f.

Section Least_fixed_theorem.

Parameter X : L->(L->L)->Ord->Pow L.
Parameter Y : L->(L->L)->Ord->Pow L.
Lemma Y_ord (v:L) (f:L->L) (b:Ord):
  Y v f b = if In_cond v (X v f b) then 
    (X v f b)∩(fun x => v⊑(b)x)
  else
    (X v f b).
Admitted.
Lemma X_zero (v:L) (f:L->L): X v f 0 = Full_set L.
Admitted.
Lemma X_succ (v:L) (f:L->L) (b:Ord):
  X v f (Succ b) = (Y v f b)∩(fun x => f x =(b) x /\
    forall y, y∈(Y v f b) -> f y ⊑(b) y -> x ⊑(b) y).
Admitted.
Lemma X_lim (v:L) (f:L->L) (a:Ord):
  Limit a -> X v f a = OrdIntersection a (X v f).
Admitted.

Theorem Least_fixed {f:L->L} (v:L):
  Stratified_monotonic f -> v ⊑ f v ->
  exists x, f x = x /\ v ⊑ x /\ forall z, v ⊑ z -> f z ⊑ z -> x ⊑ z.
Proof.
  intros.
  assert (s1:forall b, Y v f b⊆X v f b).
    intros.
    rewrite (Y_ord v f b).
    destruct (In_cond v (X v f b)).
    apply Intersection_subset.
    exact Included_reflexivity.
  assert (s2:forall b, X v f (Succ b)⊆Y v f b).
    intros.
    rewrite (X_succ v f b).
    apply Intersection_subset.
  assert (forall x {b}, b<k -> x∈(X v f (Succ b)) -> X v f (Succ b) = X v f b ∩ [x]b).
    intros.
    pose (ll_preorders b H1).
    rewrite (X_succ v f b) in H2.
    induction H2.
    destruct H3.
    apply Extentionality.
    (* X (Succ b) ⊆ X b ∩ [x] b *)
      unfold Included.
      intro y.
      intros.
      rewrite (X_succ v f b) in H5.
      apply intersection_intro.
      (* y ∈ X b *)
        apply s1.
        destruct H5.
        exact H5.
      (* y ∈ [x] b *)
        destruct H5 as [y].
        induction H6.
        destruct H3.
        destruct H6.
        split.
        exact (H4 y H5 H6).
        exact (H7 x H2 H3).
    (* X b ∩ [x] b ⊆ X (Succ b) *)
      unfold Included.
      intro z.
      intros.
      destruct H5 as [z].
      unfold Equiv_class in H6.
      unfold In in H6.
      rewrite (X_succ v f b).
      split.
      (* y ∈ Y b *)
        rewrite (Y_ord v f b).
        rewrite (Y_ord v f b) in H2.
        destruct (In_cond v (X v f b)).
        (* v ∈ X b *)
          apply intersection_intro.
          exact H5.
          unfold In.
          transitivity (x).
          destruct H2.
          exact H7.
          destruct H6.
          exact H6.
        (* ~ v ∈ X b *)
          exact H5.
      split.
      (* f z =( b) z *)
        destruct H3.
        destruct H6.
        split.
        transitivity (f x).
        apply (H b H1).
        exact H8.
        transitivity (x);assumption.
        transitivity (x).
        exact H8.
        transitivity (f x).
        exact H7.
        apply (H b H1).
        exact H6.
      (* forall y : L, y ∈ Y b -> f y ⊑( b) y -> z ⊑( b) y *)
        intros.
        transitivity (x).
        destruct H6.
        exact H9.
        exact (H4 y H7 H8).
  assert (forall a, a<k ->
      (forall c, c<a -> X v f a⊆X v f c) /\ 
      Closed (≈(a)) (X v f a) /\ 
      Complete (X v f a) /\ 
      Compatible f (X v f a)).
    apply (Tranfinite_induction (fun a => a<k ->
      (forall c, c<a -> X v f a⊆X v f c) /\ 
      Closed (≈(a)) (X v f a) /\ 
      Complete (X v f a) /\ 
      Compatible f (X v f a))).
    (* a=0 *)
      rewrite X_zero.
      intros.
      split.
      (* forall c : Ord, c < 0 -> Full_set L ⊆ X c *)
        intros.
        case (Ord_no_lt_zero H3).
      split.
      (* Closed (≈( 0)) (Full_set L) *)
        unfold Closed.
        unfold Approx.
        intros.
        case (Ord_no_lt_zero H5).
      split.
      (* Complete (Full_set L) *)
        unfold Complete.
        split.
        apply (Has_something_then_not_empty v).
        apply (full_intro).
        intros.
        split;apply (full_intro).
      (* Compatible f (Full_set L) *)
        unfold Compatible.
        intros.
        apply (full_intro).
    (* succ *)
      intro b.
      intros.
      pose ((Ord_lt_transitivity (Ord_succ_gt b) H3)).
      pose (H2 o).
      destruct a.
      destruct H5.
      destruct H6.
      split.
      (* forall c : Ord, c < Succ b -> X (Succ b) ⊆ X c *)
        intros.
        apply (Included_transitivity (X v f b)).
        (* X (Succ b) ⊆ X b *)
          apply (Included_transitivity (Y v f b)).
          exact (s2 b).
          exact (s1 b).
        (* X b ⊆ X c *)
          destruct (Ord_lt_total b c).
          case (Ord_no_between_succ H9 H8).
          destruct H9.
          rewrite H9.
          exact Included_reflexivity.
          exact (H4 c H9).
      pose (Complete_and_closed_prelattice o H6 H5).
      assert (CompletePrelattice (⊑(b)) (Y v f b) /\ Compatible f (Y v f b)).
        rewrite (Y_ord v f b).
        destruct (In_cond v (X v f b)).
        split.
        exact (Subprelattice i c).
        (* Compatible f (X b ∩ (fun x : L => v ⊑( b) x)) *)
          unfold Compatible.
          intros.
          induction H8.
          split.
          exact (H7 x H8).
          unfold In.
          transitivity (f v).
          exact (Alpha o H0 (H5 v (f v) i (H7 v i))).
          apply (H b o).
          exact H9.
        split;assumption.
      destruct H8.
      destruct (Knaster_tarski H8 H9 (H b o)).
      destruct H10.
      destruct H11.
      destruct H12.
      assert (X v f (Succ b) = X v f b ∩ [x] b).
        apply (H1 x b o).
        rewrite (X_succ v f b).
        split.
        exact H10.
        split.
        split;assumption.
        exact H13.
      rewrite H14.
      split.
      (* Closed *)
        unfold Closed.
        intros.
        induction H15.
        destruct H17.
        induction H16.
        destruct H19.
        apply (Aux_Equiv_a_approx_succ_a o).
        split;transitivity (x);assumption.
      split.
      (* Complete *)
        pose (s1 b x H10).
        exact (Class_complete o i H6).
      (* Compatible *)
        unfold Compatible.
        intros.
        induction H15.
        split.
        exact (H7 x0 H15).
        destruct H16.
        split;
          transitivity (f x);
          try apply (H b o);
          assumption.
    (* limit *)
      intros.
      rewrite (X_lim v f a H2).
      assert (a≤k).
        exact (or_introl H5).
      split.
      (* forall c : Ord, c < a -> X a ⊆ X c *)
        unfold Included.
        intros.
        induction H8.
        exact (H8 c H7).
      split.
      (* Closed *)
        apply (Cap_closed (X v f) H6 H2).
        intros.
        destruct (H4 b H7 (Ord_lt_transitivity H7 H5)).
        destruct H9.
        exact H9.
      split.
      (* Complete *)
        assert (OrdIntersection a (X v f)<>Empty_set L).
          apply (Cap_not_empty (X v f) H6 H2).
          intros.
          destruct (H4 b H7 (Ord_lt_transitivity H7 H5)).
          destruct H9.
          destruct H10.
          exact H10.
          intros.
          destruct (H4 c H8 (Ord_lt_transitivity H8 H5)).
          exact (H9 b H7).
        refine (Cap_complete (X v f) H6 H2 _ H7).
        intros.
        destruct (H4 b H8 (Ord_lt_transitivity H8 H5)).
        destruct H10.
        destruct H11.
        exact H11.
      (* Compatible *)
        apply (Cap_compatible (X v f) H6).
        intros.
        destruct (H4 b H7 (Ord_lt_transitivity H7 H5)).
        destruct H9.
        destruct H10.
        exact H11.
  pose (Xk:=OrdIntersection k (X v f)).
  assert (k≤k).
    apply or_intror.
    reflexivity.
  assert (Xk<>Empty_set L).
    apply (Cap_not_empty (X v f) H3 k_limit).
    (* forall b : Ord, b < k -> Complete (X b) *)
      intros.
      destruct (H2 b H4).
      destruct H6.
      destruct H7.
      exact H7.
    (* forall b c : Ord, b < c -> c < k -> X c ⊆ X b *)
      intros.
      destruct (H2 c H5).
      exact (H6 b H4).
  assert (Closed (≈(k)) Xk).
    apply (Cap_closed (X v f) H3 k_limit).
    intros.
    destruct (H2 b H5).
    destruct H7.
    exact H7.
  assert (Compatible f Xk).
    apply (Cap_compatible (X v f) H3).
    intros.
    destruct (H2 b H6).
    destruct H8.
    destruct H9.
    exact H10.
  destruct (Not_empty_then_has_something H4).
  assert (forall y, (y∈Xk) -> y=x).
    intros.
    apply property2.
    apply H5;assumption.
  exists x.
  split.
  (* f x = x *)
    apply H8.
    exact (H6 x H7).
  split.
  (* v ⊑ x *)
    destruct (LEM (forall a, a<k -> v∈X v f a)).
    (* forall a : Ord, v ∈ X a *)
      assert (v∈Xk).
        apply ord_intersection_intro.
        exact H9.
      rewrite (H8 v H10).
      reflexivity.
    (*  ~ (forall a : Ord, a < k -> v ∈ X a) *)
      apply Ord_lt_wf2 in H9.
      destruct H9 as [a].
      destruct H9.
      destruct (Not_imply H9).
      destruct (Ord_limit_cond a).
      (* Successor a *)
        destruct s as [b].
        rewrite H13 in H10.
        rewrite H13 in H11.
        pose (Ord_lt_transitivity (Ord_succ_gt b) H11).
        pose (H10 b (Ord_succ_gt b) o).
        induction H7.
        pose (H7 (Succ b) H11).
        assert (v ⊑( b) x ).
          rewrite (X_succ v f b) in i0.
          induction i0.
          rewrite (Y_ord v f b) in H14.
          destruct (In_cond v (X v f b)).
          induction H14.
          exact H16.
          case (n i).
        assert(v ⊏ x).
          apply (sqlt_determined2 v x b o).
          split.
          exact H14.
          unfold not.
          intros.
          assert (v∈X v f a).
            rewrite H13.
            rewrite (H1 x b o i0).
            split.
            exact i.
            split;assumption.
          case (H12 H16).
        destruct H15.
        exact H15.
      (* Limit a *)
        assert (v∈X v f a).
          rewrite (X_lim v f a l).
          apply ord_intersection_intro.
          intros.
          exact (H10 b H13 (Ord_lt_transitivity H13 H11)).
        case (H12 H13).
  (* forall z : L, v ⊑ z -> f z ⊑ z -> z ⊑ x *)
    intros.
    destruct (LEM (forall a, a<k -> z∈X v f a)).
    (* forall a : Ord, z ∈ X a *)
      assert (z∈Xk).
        apply ord_intersection_intro.
        exact H11.
      rewrite (H8 z H12).
      reflexivity.
    (*  ~ (forall a : Ord, a < k -> v ∈ X a) *)
      apply Ord_lt_wf2 in H11.
      destruct H11 as [a].
      destruct H11.
      destruct (Not_imply H11).
      destruct (Ord_limit_cond a).
      (* Successor a *)
        destruct s as [b].
        rewrite H15 in H12.
        rewrite H15 in H13.
        pose (Ord_lt_transitivity (Ord_succ_gt b) H13).
        pose (H12 b (Ord_succ_gt b) o).
        induction H7.
        pose (H7 (Succ b) H13).
        assert (x ⊑(b) z).
          rewrite (X_succ v f b) in i0.
          induction i0.
          destruct H17.
          apply H18.
          (* z ∈ Y b *)
            rewrite (Y_ord v f b).
            destruct (In_cond v (X v f b)).
            split.
            exact i.
            apply (Alpha (Ord_lt_transitivity (Ord_succ_gt b) H13) H9).
            destruct (H2 b (Ord_lt_transitivity (Ord_succ_gt b) H13)).
            destruct H20.
            apply (H20 v z i0 i).
            exact i.
          (* f z ⊑( b) z *)
            apply (Alpha (Ord_lt_transitivity (Ord_succ_gt b) H13) H10).
            destruct (H2 b (Ord_lt_transitivity (Ord_succ_gt b) H13)).
            destruct H20.
            refine (H20 (f z) z _ i).
            destruct H21.
            exact (H22 z i).
        assert(x ⊏ z).
          apply (sqlt_determined2 x z b o).
          split.
          exact H16.
          unfold not.
          intros.
          assert (z∈X v f a).
            rewrite H15.
            rewrite (H1 x b o i0).
            split.
            exact i.
            split;assumption.
          case (H14 H18).
        destruct H17.
        exact H17.
      (* Limit a *)
        assert (z∈X v f a).
          rewrite (X_lim v f a l).
          apply ord_intersection_intro.
          intros.
          exact (H12 b H15 (Ord_lt_transitivity H15 H13)).
        case (H14 H15).
Qed.

End Least_fixed_theorem.

Lemma Lub_eq_alpha {a:Ord} {X:Pow L} {x:L}:
  a<k -> x∈X -> (forall y, y∈X -> (y =(a) x \/ y ⊑ x)) -> lub X =(a) x.
Proof.
  intros.
  pose (X' := X∩[x]a).
  assert (lub X' =(a) x).
    apply (Aux_Approx_succ_a_equiv_a H).
    apply (Closed_lub (Ord_lt_limit k_limit H)).
    apply (Has_something_then_not_empty x).
    split.
    exact H0.
    exact (Aux_X_in_class_x H).
    unfold Forall_left.
    intros.
    induction H2.
    apply (Aux_Equiv_a_approx_succ_a H) in H3.
    exact (Aux_Approx_symmetric H3).
  assert (lub X = lub X').
    apply (Unique_lub X ll_cl).
    exact (fcl_lub X).
    destruct (fcl_lub X').
    split.
    (* UpperBound (⊑) (lub X') X *)
      unfold UpperBound.
      unfold Forall_left.
      intro y.
      intros.
      destruct (H1 y H5).
      (* y=(a)x *)
        apply H3.
        split.
        exact H5.
        exact (Aux_Equiv_symmetric H6).
      (*  y ⊑ x *)
        transitivity (x).
        exact H6.
        apply H3.
        split.
        exact H0.
        exact (Aux_X_in_class_x H).
    (* Least *)
      intros.
      apply (H4 y (full_intro L y)).
      apply (UpperBound_subset H6).
      exact (Intersection_subset X ([x]a)).
  rewrite H3.
  exact H2.
Qed.

Lemma Aux_Property1_leq1 {a b:Ord} {x y:L}:
  a<k -> x =(a) y -> b≤a -> x =(b) y.
Proof.
  intros.
  destruct H1.
  destruct H0.
  exact (property1 a x y H H0 b H1).
  rewrite H1.
  exact H0.
Qed.

Lemma Aux_Property1_leq2 {a b:Ord} {x y:L}:
  a<k -> x ⊑(a) y -> b≤a -> x ⊑(b) y.
Proof.
  intros.
  destruct H1.
  apply property1 in H0.
  destruct (H0 b H1).
  exact H2.
  exact H.
  rewrite H1.
  exact H0.
Qed.

Lemma Aux_Not_equiv {a:Ord} {x y:L}:
  ~ (x ⊑(a) y) -> ~ (x =(a) y).
Proof.
  unfold not.
  intros.
  destruct H0.
  case (H H0).
Qed.

Lemma Sqleq_determined {a:Ord} {x y:L}:
  a<k -> x ⊏(a) y -> x ⊑ y.
Proof.
  intros.
  assert (x⊏y).
    exact (sqlt_determined2 x y a H H0).
  destruct H1.
  exact H1.
Qed.


Lemma Lub_postfixed {f:L->L} {X:Pow L}: 
  Stratified_monotonic f -> (forall x, x∈X->x⊑f x) -> lub X ⊑ f (lub X).
Proof.
  intros.
  destruct (LEM (lub X∈X)).
  (* lub X ∈ X *)
    exact (H0 (lub X) H1).
  (* ~ lub X ∈ X *)
    destruct (fcl_lub X).
    apply (H3 (f (lub X)) (full_intro L (f (lub X)))).
    unfold UpperBound.
    unfold Forall_left.
    intros.
    pose (H2 x H4).
    destruct (Aux_Sqleq_definition s).
    (* x=lub X *)
      rewrite <- H5 in H1.
      case (H1 H4).
    (* x ⊏ lub X *)
      destruct (sqlt_determined1 x (lub X) H5) as [a].
      destruct H6.
      assert (H7':=H7).
      destruct H7.
      apply (H a H6) in H7.
      destruct (Aux_Sqleqa_definition H7).
      (* f x =( a) f (lub X) *)
        assert (x ⊑ f (lub X) \/ x =(a) f (lub X)).
          destruct (Aux_Sqleq_definition (H0 x H4)).
          (* x = f x *)
            apply or_intror.
            destruct H9.
            pose (ll_preorders a H6).
            split;
              transitivity (f x);
              try assumption;
              try rewrite <- H10;
              try reflexivity.
          (* x ⊏ f x *)
            destruct (sqlt_determined1 x (f x) H10) as [b].
            destruct H11.
            destruct (Ord_leq_total_r a b).
            (* a<b *)
              destruct H12.
              destruct (property1 b x (f x) H11 H12 a H13).
              destruct H9.
              apply or_intror.
              pose (ll_preorders a H6).
              split;
                transitivity (f x);
                assumption.
            (*  b ≤ a *)
              apply or_introl.
              destruct (Aux_Property1_leq1 H6 H9 H13).
              pose (Sqsubset_circ_sqsubseteq H11 H12 H14).
              apply sqlt_determined2 in s0.
              destruct s0.
              exact H16.
              exact H11.
        destruct H10.
        exact H10.
        apply Aux_Not_equiv in H8.
        pose (Modus_tollens1 (Lub_eq_alpha H6 H4) H8).
        destruct (forall_exists3 n) as [y].
        destruct (Not_imply H11).
        destruct (De_morgan1 H13).
        destruct (Aux_Sqleq_definition (H2 y H12)).
        (* y=lub X *)
          rewrite <- H16 in H1.
          case (H1 H12).
        (* y ⊏ lub X *)
          destruct (sqlt_determined1 y (lub X) H16) as [b].
          destruct H17.
          assert (H18'':=H18).
          destruct H18.
          assert (H18':=H18).
          apply (H b H17) in H18.
          destruct (Ord_lt_total a b).
          (* a<b *)
            destruct (property1 b y (lub X) H17 H18' a H20).
            pose (Sqsubset_circ_sqsubseteq H6 H7' H22).
            assert (H21':=H21).
            apply (H a H6) in H21'.
            destruct (Aux_Sqleq_definition (H0 y H12)).
            (* y=f y *)
              apply (Sqleq_determined H6).
              rewrite H23 in s0.
              exact (Sqsubset_circ_sqsubseteq H6 s0 H21').
            (* y ⊏ f y *)
              destruct (sqlt_determined1 y (f y) H23) as [c].
              destruct H24.
              destruct (Ord_leq_total_l a c).
              (* a ≤ c *)
                destruct H25.
                pose (Aux_Property1_leq2 H24 H25 H26).
                apply (Sqleq_determined H6).
                pose (Sqsubset_circ_sqsubseteq H6 s0 s1).
                exact (Sqsubset_circ_sqsubseteq H6 s2 H21').
              (* c<a *)
                destruct s0.
                apply (Sqleq_determined H24).
                destruct (property1 a x y H6 H27 c H26).
                pose (Sqsubseteq_circ_sqsubset H24 H29 H25).
                destruct (property1 a (f y) (f (lub X)) H6 H21' c H26).
                exact (Sqsubset_circ_sqsubseteq H24 s0 H31).
          destruct H20.
          (* a=b *)
            destruct (Aux_Sqleq_definition (H0 y H12)).
            (* y = f y *)
              pose (ll_preorders a H6).
              assert (y ⊑(a) x).
                transitivity (f y).
                (* y ⊑( a) f y *)
                  rewrite <- H21.
                  reflexivity.
                transitivity (f (lub X)).
                (* f y ⊑( a) f (lub X) *)
                  rewrite H20.
                  exact H18.
                (* f (lub X) ⊑( a) x *)
                  destruct H10.
                  exact H22.
              destruct (Aux_Sqleqa_definition H22).
              case (H14 H23).
              apply sqlt_determined2 in H23.
              destruct H23.
              case (H15 H23).
              exact H6.
            (* y ⊏ f y *)
              destruct (sqlt_determined1 y (f y) H21) as [c].
              destruct H22.
              destruct (Ord_leq_total_r c a).
              (* c<a *)
                pose (ll_preorders c H22).
                assert (f y ⊑(c) x).
                  transitivity (f (lub X)).
                  (* f y ⊑( c) f (lub X) *)
                    rewrite <- H20 in H18.
                    destruct (property1 a (f y) (f (lub X)) H6 H18 c H24).
                    exact H25.
                  (* f (lub X) ⊑( c) x *)
                    destruct H10.
                    destruct (property1 a (f (lub X)) x H6 H25 c H24).
                    exact H26.
                pose (Sqsubset_circ_sqsubseteq H22 H23 H25).
                apply sqlt_determined2 in s0.
                destruct s0.
                case (H15 H26).
                exact H22.
              (* a ≤ c *)
                pose (ll_preorders a H6).
                assert (y ⊑(a) x).
                  transitivity (f y).
                  (* y ⊑( a) f y *)
                    destruct H23.
                    exact (Aux_Property1_leq2 H22 H23 H24).
                  transitivity (f (lub X)).
                  (* f y ⊑( a) f (lub X) *)
                    rewrite H20.
                    exact H18.
                  (* f (lub X) ⊑( a) x *)
                    destruct H10.
                    exact H25.
                destruct (Aux_Sqleqa_definition H25).
                case (H14 H26).
                apply sqlt_determined2 in H26.
                destruct H26.
                case (H15 H26).
                exact H6.
          (* b<a *)
            destruct H7'.
            destruct (property1 a x (lub X) H6 H21 b H20).
            pose (Sqsubset_circ_sqsubseteq H17 H18'' H24).
            apply sqlt_determined2 in s0.
            destruct s0.
            case (H15 H25).
            exact H17.
      (* f x ⊏( a) f (lub X) *)
        apply sqlt_determined2 in H9.
        destruct H9.
        transitivity (f x).
        exact (H0 x H4).
        exact H9.
        exact H6.
Qed.

Lemma Complete_lattice_definition {L:Set} (leq: L->L->Prop) (S:Pow L):
  PartialOrder leq ->
  (exists b, Bottom leq b S) ->
  (forall X:Pow L, X ⊆ S->X<>Empty_set L->(exists x, x ∈ S /\ LeastUpperBound leq S x X)) ->
  CompleteLattice leq S.
Admitted. (* DP02 2.31 *)

Lemma Aux_bottom {y:L}:
  lub (Empty_set L) ⊑ y.
Proof.
  apply (Empty_set_lub (Full_set L)).
  exact ll_cl.
  exact (fcl_lub (Empty_set L)).
  exact (full_intro L y).
Qed.

Theorem Postfixed_lattice {f:L->L}:
  Stratified_monotonic f -> CompleteLattice (⊑) (fun x => x⊑f x).
Proof.
  intros.
  apply Complete_lattice_definition.
  exact fcl_po.
  (* bottom *)
    exists (lub (Empty_set L)).
    split.
    exact (Aux_bottom).
    unfold LowerBound.
    unfold Forall_right.
    intros.
    exact (Aux_bottom).
  (* lub *)
    intros.
    exists (lub X0).
    split.
    apply (Lub_postfixed H).
    intros.
    exact (H0 x H2).
    destruct (fcl_lub X0).
    split.
    exact H2.
    intros.
    exact (H3 y (full_intro L y) H5).
Qed.

Theorem Fixed_lattice {f:L->L}:
  Stratified_monotonic f -> CompleteLattice (⊑) (fun x => f x=x).
Proof.
  intros.
  apply Complete_lattice_definition.
  exact fcl_po.
  (* bottom *)
    destruct (Least_fixed (lub (Empty_set L)) H Aux_bottom).
    destruct H0.
    destruct H1.
    exists x.
    split.
    unfold In.
    rewrite H0.
    reflexivity.
    unfold LowerBound.
    unfold Forall_right.
    intros.
    apply (H2 y Aux_bottom).
    rewrite H3.
    reflexivity.
  (* lub *)
    intro X.
    intros.
    assert (lub X ⊑ f (lub X)).
      apply (Lub_postfixed H).
      intros.
      rewrite (H0 x H2).
      reflexivity.
    destruct (Least_fixed (lub X) H H2).
    destruct H3.
    destruct H4.
    exists x.
    split.
    exact H3.
    split.
    (* UpperBoud *)
      unfold UpperBound.
      unfold Forall_left.
      intros.
      transitivity (lub X).
      destruct (fcl_lub X).
      exact (H7 x0 H6).
      exact H4.
    (* least *)
      intros.
      apply H5.
      destruct (fcl_lub X).
      exact (H9 y (full_intro L y) H7).
      rewrite H6.
      reflexivity.
Qed.

End  LexicographicLattices.




  






  
  
  
  
  
  
  
  
  
  
 





































