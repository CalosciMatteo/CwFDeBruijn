From CwFdeBruijn.Syntax.dB Require Import dB.
From CwFdeBruijn.Syntax.dB Require Export occur.

(* Refs in x are < p. *)
Definition ContextP (p : nat) (x : dB) : Prop :=
  forall i (Hi : OccurP i x), i < p.

Lemma ContextP_ref {p i} (H : i < p) : ContextP p (dB_ref i).
Proof.
red. inversion 1 using OccurP_ref_inversion. assumption.
Qed.

Lemma ContextP_index {p i} (Hx : ContextP p (dB_ref i)) : i < p.
Proof.
red in Hx. apply Hx. apply OccurP_ref.
Qed.

Lemma ContextP_app {p x y} (Hx : ContextP p x) (Hy : ContextP p y) :
  ContextP p (dB_app x y).
Proof.
red. intros i Hi.
inversion Hi using OccurP_app_inversion; auto.
Qed.

Lemma ContextP_lam {p x} (Hx : ContextP (S p) x) :
  ContextP p (dB_lam x).
Proof.
red. intros i Hi.
cut (S i < S p).
1:{ lia. }
apply Hx.
inversion Hi using OccurP_lam_inversion; auto.
Qed.

Lemma ContextP_rator {p x y} (H : ContextP p (dB_app x y)) : ContextP p x.
Proof.
red. intros i Hi.
red in H.
apply H. apply OccurP_rator. exact Hi.
Qed.

Lemma ContextP_rand {p x y} (H : ContextP p (dB_app x y)) : ContextP p y.
Proof.
red. intros i Hi.
red in H.
apply H. apply OccurP_rand. exact Hi.
Qed.

Lemma ContextP_body {p x} (H : ContextP p (dB_lam x)) : ContextP (S p) x.
Proof.
red. intros i Hi.
red in H.
destruct i as [|i].
1:{ lia. }
rewrite <-Nat.succ_lt_mono.
apply H. apply OccurP_body. exact Hi.
Qed.

Lemma ContextP_reindex {x} : forall {p} (Hx : ContextP p x)
  {f} q (Hf : forall i, i < p -> f i < q),
  ContextP q (reindex f x).
Proof.
red. intros.
apply OccurP_reindex_inversion in Hi.
destruct Hi as (j, (Hj, Hi)).
subst i.
apply Hf.
unfold ContextP in Hx.
apply Hx.
assumption.
Qed.

Lemma ContextP_reindex_S {x} : forall {p} (Hx : ContextP p x),
  ContextP (S p) (reindex S x).
Proof.
intros.
eapply ContextP_reindex.
exact Hx.
lia.
Qed.


(* AssignP:
  AssignP p q δ means that (p,q) is a support for δ *)
Record AssignP (p q : nat) (δ : nat -> dB) : Prop := AssignP_proof {
  AssignP_lt : (forall i, i < q -> ContextP p (δ i));
  AssignP_ge : (forall i, q <= i -> δ i = dB_ref ((i + p) - q))
}.

(* Tms_id p : Tms Γ Γ *)
Lemma AssignP_id (p : nat) : AssignP p p dB_ref.
Proof.
split.
- intros. apply ContextP_ref. assumption.
- intros i Hi. f_equal. lia.
Qed.

(* ϵ : Tms Γ • *)
Lemma AssignP_nil (p : nat) : AssignP p 0 (fun i => dB_ref (p + i)).
Proof.
apply AssignP_proof.
- intros. lia.
- intros. f_equal. lia.
Qed.

(* Tms_snoc {p q : nat} (δ : Tms p q) (x : Tm p) : Tms p (S q) *)
Lemma AssignP_snoc p q δ (Hδ : AssignP p q δ) x (Hx : ContextP p x) :
  AssignP p (S q) (dB_snoc δ x).
Proof.
apply AssignP_proof.
- intros [|i] lt.
  + simpl. assumption.
  + simpl. eapply AssignP_lt. eassumption. lia.
- intros [|i] lt.
  + simpl. lia.
  + simpl. apply AssignP_ge. assumption. lia.
Qed.

Lemma AssignP_lift {p q δ} (Hδ : AssignP p q δ) :
  AssignP (S p) (S q) (lift δ).
Proof.
apply AssignP_proof.
- intros i Hi.
  destruct i as [|i].
  + simpl. apply ContextP_ref. lia.
  + simpl. apply ContextP_reindex_S.
    destruct Hδ as (Hδ1, Hδ2).
    apply Hδ1.
    rewrite Nat.succ_lt_mono. exact Hi.
- destruct i.
  + lia.
  + intros.
    apply le_S_n in H.
    simpl.
    destruct Hδ as (Hδ1, Hδ2).
    assert (Hδ2_ := Hδ2 _ H).
    rewrite Hδ2_. simpl. f_equal. lia.
Qed.

Lemma ContextP_subst x :
  forall q (Hx : ContextP q x) δ p (Hδ : AssignP p q δ),
  ContextP p (dB_subst δ x).
Proof.
induction x as [j| x Hx y Hy | x Hx].
- intros.
  apply ContextP_index in Hx.
  assert (Hj2 : j < q).
  { assert (HH : forall i, i = j -> i < q).
    { intros. subst i. exact Hx. }
    apply HH. reflexivity.
  } clear Hx.
  simpl.
  destruct Hδ as (Hδ1, Hδ2).
  apply Hδ1 in Hj2.
  exact Hj2.
- simpl. intros q Hxy δ p.
  intros Hδ.
  apply ContextP_app.
  + eapply Hx. 2: exact Hδ. apply ContextP_rator in Hxy. exact Hxy.
  + eapply Hy. 2: exact Hδ. apply ContextP_rand in Hxy. exact Hxy.
- intros q Hlam. apply ContextP_body in Hlam.
  intros δ p Hδ.
  assert (Hx0 := Hx _ Hlam).
  clear Hx Hlam.
  simpl.
  apply ContextP_lam.
  apply Hx0.
  apply AssignP_lift. exact Hδ.
Qed.

(* assign_comp {q r} (δ₁ : Tms q r) {p} (δ₂ : Tms p q) : Tms p r *)
Lemma AssignP_comp
  {q r} δ₁ (Hδ₁ : AssignP q r δ₁)
  {p} δ₂ (Hδ₂ : AssignP p q δ₂) :
  AssignP p r (assign_comp δ₁ δ₂).
Proof.
apply AssignP_proof.
- intros i Hlt. unfold assign_comp.
  eapply ContextP_subst. 2: exact Hδ₂.
  eapply AssignP_lt; eauto.
- intros i Hle. unfold assign_comp.
  destruct Hδ₁ as (_, Hδ₁).
  assert (H := Hδ₁ _ Hle).
  rewrite H. simpl.
  destruct Hδ₂ as (_, Hδ₂).
  rewrite Hδ₂. 2: lia.
  f_equal. lia.
Qed.

Definition assign_π₂ (δ : nat -> dB) : dB := δ 0.

(* assign_π₂ {p q} (δ : Tms p (S q)) : Tm p *)
Lemma ContextP_π₂ {p q} δ (Hδ : AssignP p (S q) δ) : ContextP p (assign_π₂ δ).
Proof.
  unfold assign_π₂.
  destruct Hδ as (H, _).
  apply H. lia.
Qed.

(* assign_π₁ {p q} (δ : Tms p (S q)) : Tms p q *)
Lemma AssignP_π₁ {p q} δ (Hδ : AssignP p (S q) δ) : AssignP p q (assign_π₁ δ).
Proof.
apply AssignP_proof.
- intros i Hlt.
  destruct Hδ as (H,_).
  assert (H1 := H (S i)).
  unfold assign_π₁.
  apply H1. lia.
- intros i Hle.
  destruct Hδ as (_,H).
  unfold assign_π₁.
  rewrite H. 2: lia.
  reflexivity.
Qed.

Definition dBtm p : Type := {x : dB & ContextP p x}.

Definition dBtms p q : Type := {δ : nat -> dB & AssignP p q δ}.