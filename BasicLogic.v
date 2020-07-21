(*Law of excluded middle*)
Axiom LEM: forall P:Prop, P\/~P.

Lemma Modus_tollens1 {P Q:Prop}: (P->Q)->~Q->~P.
Proof.
  unfold not.
  intros.
  apply (H0 (H H1)).
Qed.

Lemma Modus_tollens2 {P Q:Prop}: (P->~Q)->Q->~P.
Proof.
  unfold not.
  intros.
  apply (H H1 H0).
Qed.

Lemma Modus_tollens3 {P Q: Prop}: (~P->Q)->~Q->P.
Proof.
  unfold not.
  intros.
  pose (LEM P).
  destruct o.
  exact H1.
  case (H0 (H H1)).
Qed.

Lemma Modus_tollens4 {P Q: Prop}: (~P->~Q)->Q->P.
Proof.
  unfold not.
  intros.
  pose (LEM P).
  destruct o.
  exact H1.
  case (H H1 H0).
Qed.


Lemma exists_forall1 {L:Set} {P:L->Prop}:(exists x, P x)->(~forall x, ~P x).
Proof.
  unfold not.
  intros.
  destruct H.
  apply (H0 x H).
Qed.

Lemma exists_forall2 {L:Set} {P:L->Prop}:(~exists x, P x)->(forall x, ~P x).
Proof.
  unfold not.
  intros.
  apply H.
  exists x.
  exact H0.
Qed.

Lemma exists_forall3 {L:Set} {P:L->Prop}:(exists x, ~P x)->(~forall x, P x).
Proof.
  unfold not.
  intros.
  destruct H.
  case (H (H0 x)).
Qed.

Lemma exists_forall4 {L:Set} {P:L->Prop}:(~exists x, ~P x)->(forall x, P x).
Proof.
  unfold not.
  intros.
  destruct (LEM (P x)).
  exact H0.
  destruct H.
  exists x.
  exact H0.
Qed.

Lemma forall_exists1 {L:Set} {P:L->Prop}:(forall x, ~P x)->(~exists x, P x).
Proof.
  intros.
  exact (Modus_tollens2 exists_forall1 H).
Qed.


Lemma forall_exists2 {L:Set} {P:L->Prop}:(~forall x, ~P x)->(exists x, P x).
Proof.
  intros.
  exact (Modus_tollens3 exists_forall2 H).
Qed.

Lemma forall_exists3 {L:Set} {P:L->Prop}:(~forall x, P x)->(exists x, ~P x).
Proof.
  intros.
  exact (Modus_tollens3 exists_forall4 H).
Qed.

Lemma forall_exists4 {L:Set} {P:L->Prop}:(forall x, P x)->(~exists x, ~P x).
Proof.
  intros.
  exact (Modus_tollens2 exists_forall3 H).
Qed.

Lemma PNNP {P:Prop}: P->~~P.
Proof.
  unfold not.
  intros.
  exact (H0 H).
Qed.

Lemma NNPP {P:Prop}: ~~P->P.
Proof.
  intros.
  destruct (LEM P).
  exact H0.
  case (H H0).
Qed.

Lemma Not_imply {P Q:Prop}:
  ~(P->Q)->(P/\~Q).
Proof.
  intros.
  split.
  apply NNPP.
  unfold not.
  intros.
  apply H.
  intros.
  case (H0 H1).
  unfold not.
  intros.
  apply H.
  intros.
  exact H0.
Qed.

Lemma De_morgan1 {P Q:Prop}:
  ~(P \/ Q)-> ~P /\ ~Q.
Proof.
  unfold not.
  intros.
  split;
    intro;
    apply H.
  exact (or_introl H0).
  exact (or_intror H0).
Qed.
  
Lemma De_morgan2 {P Q:Prop}:
  ~(P /\ Q)-> ~P \/ ~Q.
Proof.
  unfold not.
  intros.
  destruct (LEM P).
  right.
  intros.
  apply H.
  split; assumption.
  exact (or_introl H0).
Qed.