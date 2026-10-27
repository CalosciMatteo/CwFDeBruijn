From CwFdeBruijn.Syntax.dB Require Import dB dBasMwM.
From CwFdeBruijn.Syntax.dB Require Export dBtm TmP.

(* TmP <-> ContextP *)

Lemma TmP_OccurP (x : dB) :
  forall p (Hx : TmP p x) i (Hi : OccurP i x), i < p.
Proof.
induction x.
- intros. apply OccurP_index in Hi. subst. apply TmP_index in Hx. assumption.
- intros. apply OccurP_app in Hi. destruct Hi as [Hi | Hi].
  + apply TmP_rator in Hx. auto.
  + apply TmP_rand in Hx. auto.
- intros. apply OccurP_lam in Hi. apply TmP_body in Hx. apply Nat.succ_lt_mono. auto.
Qed.

Lemma OccurP_TmP (x : dB) :
  forall p (Hx : forall i, OccurP i x -> i < p), TmP p x.
Proof.
induction x.
- intros. constructor. apply Hx. constructor.
- intros. constructor.
  + apply IHx1. intros. apply Hx. apply OccurP_rator. assumption.
  + apply IHx2. intros. apply Hx. apply OccurP_rand. assumption.
- intros. constructor. apply IHx. clear IHx. intros.
  destruct i.
  + lia.
  + rewrite <-Nat.succ_lt_mono. apply Hx. constructor. assumption.
Qed.

Definition TmP_iff_OccurP p (x : dB) :
  TmP p x <-> (forall i, OccurP i x -> i < p).
Proof.
split.
- intros. eapply TmP_OccurP; eauto.
- intros. apply OccurP_TmP. assumption.
Defined.

Definition TmP_iff_ContextP p (x : dB) :
  TmP p x <-> ContextP p x.
Proof.
apply TmP_iff_OccurP.
Qed.

(* Link TmsP <-> AssignP *)

Lemma TmsP_AssignP {p q δ} (Hδ : TmsP p q δ) : AssignP p q δ.
Proof.
induction Hδ.
- apply AssignP_nil.
- apply AssignP_snoc.
  + assumption.
  + apply TmP_iff_ContextP. assumption.
- apply AssignP_id.
- eapply AssignP_comp; eassumption.
- apply AssignP_π₁. assumption.
Qed.

Lemma AssignP_TmsP {q} : forall {p δ} (Hδ : AssignP p q δ), TmsP p q δ.
Proof.
induction q.
- intros.
  assert (Heq : δ = fun i => dB_ref (p + i)).
  { apply extensionality. intros i.
    destruct Hδ as (_, H).
    rewrite H. 2: lia. f_equal. lia.
  }
  rewrite Heq.
  apply TmsP_nil.
- intros.
  rewrite <- (dB_snoc_eta δ).
  apply TmsP_snoc.
  + apply IHq. apply AssignP_π₁. assumption.
  + apply TmP_iff_ContextP. eapply ContextP_π₂. eassumption.
Qed.

Lemma TmP_subst (x:dB) q (Hx : TmP q x) δ p (Hδ : AssignP p q δ) : TmP p (dB_subst δ x).
Proof.
  apply TmP_iff_ContextP.
  apply (ContextP_subst _ q).
  + apply TmP_iff_ContextP.
    exact Hx.
  + exact Hδ.
Qed.