Require Import Coq.Classes.RelationClasses.
Require Import Sets.
Require Import Ordinal.

Class Preorder {L:Set} (leq: L->L->Prop) := {
  preorder_reflexive :> Reflexive leq;
  preorder_transitive :> Transitive leq;
}.

Class PartialOrder {L:Set} (leq: L->L->Prop) := {
  po_preorder  :> Preorder leq;
  antisymmetry :>  forall {x y}, leq x y -> leq y x -> x=y;
}.

(* I define 2 kinds of complete lattices. The first kind is easier to deal with,
as the lub and glb operations are defined as function. However, when I have to
prove that a set forms a complete lattice, it isn't clear how to define these
operations as functions. Therefore, in this case I prefer the second one which
requires only the existence of these operations. *)

Class FunctionalCompleteLattice {L:Set} (leq: L->L->Prop) := {
  fcl_po  :> PartialOrder leq;
  lub     :  Pow L -> L;
  glb     :  Pow L -> L;
  fcl_lub :  forall X: Pow L, LeastUpperBound leq (Full_set L) (lub X) X;
  fcl_glb :  forall X: Pow L, GreatestLowerBound leq (Full_set L) (glb X) X;
}.

Class CompleteLattice {L:Set} (leq: L->L->Prop) (S: Pow L) := {
  cl_po  :> PartialOrder leq;
  cl_lub :  forall X: Pow L, X ⊆ S -> (exists x, x ∈ S /\ LeastUpperBound leq S x X);
  cl_glb :  forall X: Pow L, X ⊆ S -> (exists x, x ∈ S /\ GreatestLowerBound leq S x X);
}.

Class CompletePrelattice {L:Set} (leq: L->L->Prop) (S:Pow L) := {
  cpl_preorder :> Preorder leq;
  cpl_lub      :  forall X: Pow L, X ⊆ S -> (exists x, x ∈ S /\ LeastUpperBound leq S x X);
  cpl_glb      :  forall X: Pow L, X ⊆ S -> (exists x, x ∈ S /\ GreatestLowerBound leq S x X);
}.

Definition Strict {L:Set} (leq:L->L->Prop) (x y:L) := leq x y /\ ~leq y x.
Definition Equiv  {L:Set} (leq:L->L->Prop) (x y:L) := leq x y /\ leq y x.
Definition Approx {L:Set} (leq:Ord->L->L->Prop) (a:Ord) (x y:L) := forall b, b<a -> leq b x y.

Definition Equiv_class {L:Set} (equiv:L->L->Prop) (x:L) := fun y => equiv x y.

Class LexicographicLattice {L:Set} (sqleq:L->L->Prop) (k:Ord) (sqleqa:Ord->L->L->Prop) := {
  ll_cl            :> FunctionalCompleteLattice sqleq;
  ll_preorders     :> forall a, a<k -> Preorder (sqleqa a);
  k_limit          :  Limit k;
  sqlt_determined1: forall x y, Strict sqleq x y -> exists a, a<k /\ Strict (sqleqa a) x y;
  sqlt_determined2: forall x y a, a<k -> Strict (sqleqa a) x y -> Strict sqleq x y;
  property1        : forall a x y, a<k -> sqleqa a x y -> Approx (fun b => Equiv (sqleqa b)) a x y;
  property2        : forall x y, Approx (fun b => Equiv (sqleqa b)) k x y -> x=y;
  property3_lub    : forall x a, Equiv (sqleqa a) (lub (Equiv_class (Equiv (sqleqa a)) x)) x;
  property3_glb    : forall x a, Equiv (sqleqa a) (glb (Equiv_class (Equiv (sqleqa a)) x)) x;
}.

Lemma Unique_lub {L:Set} {leq:L->L->Prop} (X:Pow L) {x y:L}:
  (FunctionalCompleteLattice leq) ->
  LeastUpperBound leq (Full_set L) x X ->
  LeastUpperBound leq (Full_set L) y X ->
  x = y.
Proof.
  intros.
  destruct H.
  destruct H0.
  apply antisymmetry.
  exact (H1 y (full_intro L y) H0).
  exact (H2 x (full_intro L x) H).
Qed.

Lemma Empty_set_lub {L:Set} {leq:L->L->Prop} (X:Pow L) {x:L}:
  (FunctionalCompleteLattice leq) ->
  LeastUpperBound leq X x (Empty_set L) ->
  forall y, y∈X -> leq x y.
Proof.
  intros.
  destruct H.
  apply (H1 y H0).
  unfold UpperBound.
  unfold Forall_left.
  intros.
  induction H2.
Qed.

