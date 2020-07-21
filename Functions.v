Require Import Sets.

Definition Monotonic {L:Set} (rel:L->L->Prop) (f:L->L) := forall x y, rel x y -> rel (f x) (f y).

Definition Compatible {L:Set} (f:L->L) (S: Pow L) := forall x, x ∈ S -> (f x) ∈ S.
