From CwFdeBruijn.Syntax.AKcf Require Import AKcf_Conv normalization.
From Stdlib Require Import Relations.
Require Import Classes.RelationClasses.
From CwFdeBruijn.Syntax Require Import Immersions.dBToAKcf.
From CwFdeBruijn.Syntax.AKcf Require Import AKcf_Conv normalization nf_uniqueness.


Set Warnings "-notation-overridden, -parsing".
From mathcomp Require Import boot.
Set Warnings "notation-overridden, parsing".
From HB Require Import structures.

Local Open Scope quotient_scope.


Definition Tmscfσeq (δ σ : Tmscf) : bool.
Proof.
  apply (Tmscf_beq (nffun (Tmscf_normalization δ)) (nffun (Tmscf_normalization σ))).
Defined.

Definition TmscfσQ := {η | normal_form Tmscfσstep η }.

Definition TmscfσQ_pi (δ : Tmscf) : TmscfσQ
  := exist _ (nffun (Tmscf_normalization δ)) (nffun_isnf (Tmscf_normalization δ)).
Definition TmscfσQ_repr : TmscfσQ -> Tmscf := @proj1_sig _ _.

Lemma TmscfσQ_cancel : ssrfun.cancel TmscfσQ_repr TmscfσQ_pi.
Proof.
  intros cδ.
  unfold TmscfσQ_repr, TmscfσQ_pi.
  apply eq_sig_hprop.
  { intro. apply proof_irrelevance. }
  apply (Tmscf_nf_uniqueness (sval cδ) _ (sval cδ)).
  - apply svalP.
  - apply svalP.
  - apply nffun_conv.
  - autored.
Qed.

Definition TmscfσQ_eq (δ σ : TmscfσQ) : bool
  := Tmscf_beq (TmscfσQ_repr δ) (TmscfσQ_repr σ).

Definition TmscfσQ_eq_spec (δ σ : TmscfσQ) : reflect (δ = σ) (TmscfσQ_eq δ σ).
Proof.
  apply iff_reflect.
  split.
  - intro e. induction e.
    unfold TmscfσQ_eq.
    apply (introT (Tmscf_eq_spec _ _)).
    reflexivity.
  - intro arg.
    rewrite <-(TmscfσQ_cancel δ).
    rewrite <-(TmscfσQ_cancel σ).
    f_equal.
    apply (elimT (Tmscf_eq_spec _ _) arg).
Qed.

HB.instance Definition _ := isQuotient.Build Tmscf TmscfσQ TmscfσQ_cancel.

HB.instance Definition _ := hasDecEq.Build TmscfσQ TmscfσQ_eq_spec.

Lemma Tmscfσeq_coherence : {mono \pi_(TmscfσQ)%qT : x y / Tmscfσeq x y >-> x == y}.
Proof.
  by rewrite [@pi]unlock.
Qed.

HB.instance Definition _ := isEqQuotient.Build Tmscf Tmscfσeq TmscfσQ Tmscfσeq_coherence.

(**********)

Definition Tmcfσeq (x y : Tmcf) : bool.
Proof.
  apply (Tmcf_beq (nffun (Tmcf_normalization x)) (nffun (Tmcf_normalization y))).
Defined.

Definition TmcfσQ := {x | normal_form Tmcfσstep x }.

Definition TmcfσQ_pi (x : Tmcf) : TmcfσQ
  := exist _ (nffun (Tmcf_normalization x)) (nffun_isnf (Tmcf_normalization x)).

Definition TmcfσQ_repr : TmcfσQ -> Tmcf := @proj1_sig _ _.

Lemma TmcfσQ_cancel : ssrfun.cancel TmcfσQ_repr TmcfσQ_pi.
Proof.
  intros cδ.
  unfold TmscfσQ_repr, TmscfσQ_pi.
  apply eq_sig_hprop.
  { intro. apply proof_irrelevance. }
  apply (Tmcf_nf_uniqueness (sval cδ) _ (sval cδ)).
  - apply svalP.
  - apply svalP.
  - apply nffun_conv.
  - autored.
Qed.

Definition TmcfσQ_eq (x y : TmcfσQ) : bool
  := Tmcf_beq (TmcfσQ_repr x) (TmcfσQ_repr y).

Definition TmcfσQ_eq_spec (x y : TmcfσQ) : reflect (x = y) (TmcfσQ_eq x y).
Proof.
  apply iff_reflect.
  split.
  - intro e. induction e.
    unfold TmscfσQ_eq.
    apply (introT (Tmcf_eq_spec _ _)).
    reflexivity.
  - intro arg.
    rewrite <-(TmcfσQ_cancel x).
    rewrite <-(TmcfσQ_cancel y).
    f_equal.
    apply (elimT (Tmcf_eq_spec _ _) arg).
Qed.

HB.instance Definition _ := isQuotient.Build Tmcf TmcfσQ TmcfσQ_cancel.

HB.instance Definition _ := hasDecEq.Build TmcfσQ TmcfσQ_eq_spec.

Lemma Tmcfσeq_coherence : {mono \pi_(TmcfσQ)%qT : x y / Tmcfσeq x y >-> x == y}.
Proof.
  by rewrite [@pi]unlock.
Qed.

HB.instance Definition _ := isEqQuotient.Build Tmcf Tmcfσeq TmcfσQ Tmcfσeq_coherence.



(*****************************)


Lemma pi_morph21
  {T1 T2 U : Type} {qT1 : quotType T1} {qT2 : quotType T2} {qU : quotType U}
  {h : T1 -> T2 -> U} {hq : qT1 -> qT2 -> qU}
  (pi_h : forall (x : T1) (y : T2), \pi_qU (h x y) = hq (\pi_qT1 x) (\pi_qT2 y))
  (a :T1) (b :T2) (x : equal_to (\pi_qT1 a)) (y : equal_to (\pi_qT2 b))
  : \pi_qU (h a b) = hq (equal_val x) (equal_val y).
Proof. by rewrite !piE. Qed.

Notation lift_op21 Q1 Q2 Q3 g :=
  (locked (fun (x:Q1) (y:Q2) => \pi_Q3 (g (repr x) (repr y)) : Q3)).

Notation PiMorph21 pi_h :=
  (fun a b (x : {pi a}) (y : {pi b}) => EqualTo (pi_morph21 pi_h a b x y)).