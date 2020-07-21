Require Import BasicLogic.
Require Import Sets.

Parameter Ord: Set.

Parameter Zero: Ord.
Notation "0" := (Zero).

Parameter Succ: Ord -> Ord.

Definition Successor (a: Ord): Prop := exists b, a = Succ b.
Definition Limit (a: Ord): Prop := ~exists b, a = Succ b.

Parameter Ord_lt: Ord -> Ord -> Prop.
Notation "(<)" := Ord_lt.
Notation "a '<' b" := (Ord_lt a b) (at level 70).
Definition Ord_leq (a b: Ord) := a<b \/ a=b.
Notation "a '≤' b" := (Ord_leq a b) (at level 50).

Axiom Ord_lt_transitivity: forall {a b c}, a<b->b<c->a<c.

Axiom Ord_lt_strict: forall {a}, ~(a<a).

Axiom Ord_lt_total: forall a b, a < b \/ a=b \/ b < a.

Lemma Ord_leq_total_l a b: a≤b \/ b<a.
Proof.
  intros.
  pose (Ord_lt_total a b).
  destruct o.
  exact (or_introl (or_introl H)).
  destruct H.
  exact (or_introl (or_intror H)).
  exact (or_intror H).
Qed.

Lemma Ord_leq_total_r a b: a<b \/ b≤a.
Proof.
  intros.
  pose (Ord_lt_total a b).
  destruct o.
  exact (or_introl H).
  destruct H.
  repeat (apply or_intror); rewrite H; reflexivity.
  exact (or_intror (or_introl H)).
Qed.

Axiom Ord_zero_smallest: forall a, 0≤a.

Lemma Ord_no_lt_zero {a:Ord}: ~a<0.
Proof.
  unfold not.
  intros.
  destruct (Ord_zero_smallest a).
  case (Ord_lt_strict (Ord_lt_transitivity H H0)).
  rewrite H0 in H.
  case (Ord_lt_strict H).
Qed.

Axiom Ord_succ_gt : forall a, a < Succ a.

Axiom Ord_gt_succ_geq: forall {a b}, a<b -> (Succ a)≤b.

Lemma Ord_eq_succs {a b:Ord}: Succ a = Succ b -> a=b.
Proof.
  intros.
  destruct (Ord_lt_total a b).
  apply Ord_gt_succ_geq in H0.
  rewrite H in H0.
  pose (Ord_succ_gt b).
  destruct H0.
  case (Ord_lt_strict (Ord_lt_transitivity o H0)).
  rewrite H0 in o.
  case (Ord_lt_strict o).
  destruct H0.
  exact H0.
  apply Ord_gt_succ_geq in H0.
  rewrite <- H in H0.
  pose (Ord_succ_gt a).
  destruct H0.
  case (Ord_lt_strict (Ord_lt_transitivity o H0)).
  rewrite H0 in o.
  case (Ord_lt_strict o).
Qed.


Lemma Ord_lt_succ {a b:Ord}:
  b<Succ a -> b≤a.
Proof.
  intros.
  destruct (Ord_leq_total_l b a).
  exact H0.
  destruct (Ord_gt_succ_geq H0).
  case (Ord_lt_strict (Ord_lt_transitivity H H1)).
  rewrite H1 in H.
  case (Ord_lt_strict H).
Qed.

Lemma Ord_no_between_succ {a b:Ord}:
  a<b -> b<Succ a -> False.
Proof.
  intros.
  destruct (Ord_lt_succ H0).
  pose (Ord_lt_transitivity H H1).
  case (Ord_lt_strict o).
  rewrite H1 in H.
  case (Ord_lt_strict H).
Qed.


Lemma Ord_lt_limit {a b: Ord}: 
  Limit a -> b<a -> Succ b < a.
Proof.
  intros.
  destruct (Ord_gt_succ_geq H0).
  exact H1.
  assert (Successor a).
    exists b.
    rewrite H1.
    reflexivity.
  case (H H2).
Qed.

Axiom Ord_lt_wf: forall {P:Pow Ord}, 
  P<>(Empty_set Ord) -> 
  exists a, P a /\ forall b, b < a -> ~(P b).

Lemma Ord_lt_wf2  {P:Ord->Prop}: 
~(forall a, P a) -> exists a, ~ P a /\ forall b, b<a -> P b.
Proof.
  intros.
  apply forall_exists3 in H.
  destruct H.
  assert (x∈fun a => ~P a).
    exact H.
  apply (Has_something_then_not_empty) in H0.
  apply Ord_lt_wf in H0.
  destruct H0.
  destruct H0.
  exists x0.
  split.
  exact H0.
  intros.
  exact (NNPP (H1 b H2)).
Qed.

Theorem Tranfinite_induction (P: Ord->Prop): 
  P 0 -> 
  (forall a, P a -> P (Succ a)) -> 
  (forall a, Limit a -> 0<a -> (forall b, b<a -> P b) -> P a) -> 
  forall a, P a.
Proof.
  intros; revert a.
  destruct (LEM (Complement P=Empty_set Ord)).
  (* Complement P = Empty_set *)
    rewrite <- Full_complement in H2.
    apply Same_complement in H2.
    rewrite H2.
    exact (full_intro Ord).
  (* Complement P <> Empty_set *)
    destruct (Ord_lt_wf H2) as [a].
    destruct H3.
    destruct (Ord_zero_smallest a).
    (* 0<a *)
      destruct (LEM (exists b, a = Succ b)).
      (* a is successor *)
        destruct H6 as [b].
        pose (Ord_succ_gt b).
        rewrite <- H6 in o.
        pose (Not_in_complement2 (H4 b o)).
        pose (H0 b i).
        rewrite <- H6 in p.
        case (H3 p).
      (* a is limit *)
        assert (forall b : Ord, b < a -> P b).
          intros.
          apply (NNPP (H4 b H7)).
        case (H3 (H1 a H6 H5 H7)).
    (* a=0 *)
    rewrite <- H5 in H3.
    case (H3 H).
Qed.

Inductive OrdIntersection {L:Set} (a: Ord) (X: Ord->Pow L) : Pow L :=
  ord_intersection_intro :
  forall x, (forall b, b<a -> x∈(X b)) -> x ∈ (OrdIntersection a X).
Notation "'⋂' a X" := (OrdIntersection a X) (at level 50).

Parameter Ord_zero_cond : forall a, {a=0}+{0<a}.
Parameter Ord_limit_cond : forall a, {Successor a}+{Limit a}.

(* Definition Prev (a:Ord):Ord.
  case (Ord_limit_cond a).
  intros.
  unfold Successor in s.
  destruct s as [b].
  exact b.
  intros.
  exact a.
Defined.

Lemma Ord_prev_succ (a:Ord): Prev (Succ a) = a.
Proof.
  unfold Prev.
  case (Ord_limit_cond (Succ a)).
  intros.
  destruct s as [b].
  apply Ord_eq_succs.
  rewrite e.
  reflexivity.
  intros.
  unfold Limit in l.
  case (exists_forall2 l a).
  reflexivity.
Qed. *)