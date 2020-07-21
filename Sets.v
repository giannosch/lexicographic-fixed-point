Require Import BasicLogic.

Definition Pow (L:Set) := L -> Prop.

Definition In {L:Set} (A: Pow L) (x:L) : Prop := A x.
Notation "x '∈' A" := (In A x) (at level 60).

Definition Included {L:Set} (B C:Pow L) : Prop := forall x, x ∈ B -> x ∈ C.
Notation "B '⊆' C" := (Included B C) (at level 61).

Lemma Included_reflexivity {L:Set} {A:Pow L}:
  A⊆A.
Proof.
  unfold Included.
  intros.
  exact H.
Qed.

Lemma Included_transitivity {L: Set} {A C: Pow L} (B: Pow L):
  A ⊆ B -> B ⊆ C -> A ⊆ C.
Proof.
  unfold Included.
  intros.
  apply (H0 x (H x H1)).
Qed.

Axiom Extentionality: forall {L:Set} {B C:Pow L}, B ⊆ C -> C ⊆ B -> B=C.

Inductive Union {L:Set} (B C:Pow L) : Pow L :=
  | union_introl : forall {x}, x ∈ B -> x ∈ (Union B C)
  | union_intror : forall {x}, x ∈ C -> x ∈ (Union B C).
Inductive Intersection {L:Set} (B C:Pow L) : Pow L :=
  intersection_intro :
  forall x, x ∈ B -> x ∈ C -> x ∈ (Intersection B C).
Notation "B '∪' C" := (Union B C) (at level 50, left associativity).
Notation "B '∩' C" := (Intersection B C) (at level 50, left associativity).

Lemma Intersection_subset {L:Set} (A B:Pow L): (A ∩ B) ⊆ A.
Proof.
  unfold Included.
  unfold In.
  intros.
  destruct H.
  exact H.
Qed.

Lemma Intersection_commutative {L:Set} (A B:Pow L):
  (A ∩ B) = (B ∩ A).
Proof.
  apply Extentionality;
  unfold Included;
  intros;
  induction H;
  apply intersection_intro;
  assumption;
  assumption.
Qed.


Inductive Empty_set (L:Set): Pow L :=.

Lemma Has_something_then_not_empty {L:Set} {S:Pow L} (x:L):
  x ∈ S -> S <> (Empty_set L).
Proof.
  intros.
  unfold not.
  intros.
  rewrite H0 in H.
  unfold In in H.
  induction H.
Qed.

Lemma Not_empty_then_has_something {L:Set} {S:Pow L}:
  (S <> (Empty_set L)) -> (exists x, x ∈ S).
Proof.
  unfold not.
  intros.
  apply forall_exists2.
  unfold not.
  intros.
  apply H.
  apply Extentionality;unfold Included;intros.
  case (H0 x H1).
  induction H1.
Qed.

Inductive Full_set (L:Set): Pow L :=
    full_intro : forall x:L, x ∈ (Full_set L).

Lemma Full_set_subsets {L:Set} {S: Pow L}: S ⊆ (Full_set L).
Proof.
  unfold Included.
  intros.
  exact (full_intro L x).
Qed.

Definition Forall_right {L:Set} (rel:L->L->Prop) (x:L) (Y: Pow L):Prop := forall y, y ∈ Y -> rel x y.
Definition Forall_left {L:Set} (rel:L->L->Prop) (X: Pow L) (y: L):Prop := forall x, x ∈ X -> rel x y.
Definition Forall_both {L:Set} (rel:L->L->Prop) (X: Pow L) (Y: Pow L):Prop := forall x y, x ∈ X -> y ∈ Y -> rel x y.
Notation "'FA_r' r" := (Forall_right r) (at level 30).
Notation "'FA_l' r" := (Forall_left r) (at level 30).
Notation "'FA_b' r" := (Forall_both r) (at level 30).
Notation "x 'FA_r(' r ')' Y" := (Forall_right r x Y) (at level 30).
Notation "X 'FA_l(' r ')' y" := (Forall_left r X y) (at level 30).
Notation "X 'FA_b(' r ')' Y" := (Forall_both r X Y) (at level 30).

Definition UpperBound {L:Set} (rel:L->L->Prop) (x:L) (X: Pow L) :=
  (FA_l rel) X x.
Definition LowerBound {L:Set} (rel:L->L->Prop) (x:L) (X: Pow L) :=
  (FA_r rel) x X.
Definition LeastUpperBound {L:Set} (rel:L->L->Prop) (S:Pow L) (x:L) (X: Pow L) :=
  UpperBound rel x X /\
  forall y, y ∈ S -> UpperBound rel y X -> rel x y.
Definition GreatestLowerBound {L:Set} (rel:L->L->Prop) (S:Pow L) (x:L) (X: Pow L) :=
  LowerBound rel x X /\
  forall y, y ∈ S -> LowerBound rel y X -> rel y x.
Definition Bottom {L:Set} (rel:L->L->Prop) (x:L) (X:Pow L):Prop := x ∈ X /\ LowerBound rel x X.
Definition Top {L:Set} (rel:L->L->Prop) (x:L) (X:Pow L):Prop := x ∈ X /\ UpperBound rel x X.

Lemma LowerBound_subset {L:Set} {rel:L->L->Prop} {A B: Pow L} {x:L}: 
  LowerBound rel x A -> B ⊆ A -> LowerBound rel x B.
Proof.
  unfold LowerBound.
  unfold Forall_right.
  intros.
  apply (H y (H0 y H1)).
Qed.

Lemma UpperBound_subset {L:Set} {rel:L->L->Prop} {A B: Pow L} {x:L}: 
  UpperBound rel x A -> B ⊆ A -> UpperBound rel x B.
Proof.
  unfold UpperBound.
  unfold Forall_left.
  intros.
  apply (H x0 (H0 x0 H1)).
Qed.

Definition Complement {L:Set} (P: Pow L) := fun x => ~(x ∈ P).

Lemma Not_in_complement1 {L:Set} {A: Pow L} {x: L}:
  x ∈ A -> ~x ∈ Complement A.
Proof.
  exact PNNP.
Qed.

Lemma Not_in_complement2 {L:Set} {A: Pow L} {x: L}:
  ~x ∈ Complement A -> x ∈ A.
Proof.
  exact NNPP.
Qed.

Lemma Double_complement {L:Set} {A: Pow L}:
  Complement (Complement A) = A.
Proof.
  apply Extentionality; unfold Included; intros.
  apply Not_in_complement2.
  exact (Modus_tollens2 Not_in_complement1 H).
  apply (Modus_tollens3 Not_in_complement2).
  exact (Not_in_complement1 H).
Qed.

Lemma Same_complement {L:Set} (A B: Pow L):
  Complement A = Complement B -> A=B.
Proof.
  intros.
  apply Extentionality;unfold Included;intros.
  apply Not_in_complement2.
  rewrite <- H.
  apply (Not_in_complement1 H0).
  apply Not_in_complement2.
  rewrite H.
  apply (Not_in_complement1 H0).
Qed.

Lemma Empty_complement {L:Set}:
  Complement (Empty_set L) = (Full_set L).
Proof.
  unfold Complement.
  apply Extentionality;unfold Included;intros.
  exact (full_intro L x).
  unfold not.
  unfold In.
  intros.
  induction H0.
Qed.

Lemma Full_complement {L:Set}:
  Complement (Full_set L) = (Empty_set L).
Proof.
  apply Same_complement.
  rewrite Empty_complement.
  exact Double_complement.
Qed.

Parameter In_cond : forall {L:Set} (x:L) (X:Pow L), {x∈X}+{~x∈X}.




