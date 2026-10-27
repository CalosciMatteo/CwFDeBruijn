From CwFdeBruijn.Syntax.dB Require Import dB.

Fixpoint dB_depth (x:dB) : nat :=
match x with
  | dB_ref i => 0
  | dB_app x y => S (max (dB_depth x) (dB_depth y))
  | dB_lam x => S ((dB_depth x))
end.

Definition dB_depth_wf_rect (x:dB) :
  forall (P: dB -> Type)
    (IHx : forall y,
      (forall y', dB_depth y' < dB_depth y -> P y')
      -> P y),
  P x.
Proof.
  intros P IHx.
  remember (dB_depth x) as n.
  revert x Heqn.
  induction n as [m IH] using lt_wf_rect.
  intros x Heqn.
  subst.
  apply IHx.
  intros.
  eapply (IH (dB_depth y')).
  - assumption.
  - reflexivity.
Qed.

Lemma dB_depth_reindex (x:dB) (f:nat -> nat)
  : dB_depth (reindex f x) = dB_depth x.
Proof.
  revert f; induction x; intros f; simpl; auto.
Qed.