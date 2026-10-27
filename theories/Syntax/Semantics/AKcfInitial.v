From CwFdeBruijn.Syntax Require Import Semantics.Kmm
  Semantics.Monoid
  Semantics.Module
  Semantics.AKcf
  Quotients.AKcfQuot
  AKcf.AKcf_Conv
  AKcf.values
  AKcf.normalization.

Set Warnings "-notation-overridden, -parsing".
From mathcomp Require Import boot.
Set Warnings "notation-overridden, parsing".

Local Open Scope quotient_scope.

Section Initiality.

Context (H : KMMλappmodel).

Fixpoint AKcf_Initial_mndmor' (δ: Tmscf) {struct δ} : kmm_mnd H :=
match δ with
  | Tmscf_snoc δ x =>
      (kmm_snoc H (AKcf_Initial_mndmor' δ, AKcf_Initial_modmor' x))
  | Tmscf_id  => kmm_id H
  | Tmscf_comp δ σ => kmm_comp H (AKcf_Initial_mndmor' δ, AKcf_Initial_mndmor' σ)
  | Tmscf_π₁ δ => kmm_pi1 H (AKcf_Initial_mndmor' δ)
end
with AKcf_Initial_modmor' (x : Tmcf) : H :=
match x with
  | Tmcf_subst x δ => kmm_subst H (AKcf_Initial_modmor' x,  AKcf_Initial_mndmor' δ)
  | Tmcf_π₂ δ => Pi2ProdMod ((kiso H) (AKcf_Initial_mndmor' δ))
  | Tmcf_app x y => kmm_app (AKcf_Initial_modmor' x,AKcf_Initial_modmor' y)
  (*TODO: require that H satisfy the signature for app and lam*)
  | Tmcf_lam x => kmm_lam (AKcf_Initial_modmor' x)
end.

Lemma AKcf_Initial_mndmor'_step' {δ σ : Tmscf} (step : Tmscfσstep' δ σ)
  : AKcf_Initial_mndmor' δ = AKcf_Initial_mndmor' σ.
Proof.
  induction step.
  - refine (equal_f (kmm_idl H) (tt,_)).
  - refine (equal_f (kmm_idr H) (_,tt)).
  - cbn.
    symmetry. (*TODO: allign convention*)
    refine (equal_f (kmm_ass H) ((_,_),_)).
  - refine (equal_f (kmm_snocomp H) (_,_)).
  - refine (equal_f (kmm_pi1snoc H) _).
  - refine (equal_f (kmm_pi1_lin H) (_,_)).
  - refine (equal_f (kmm_snoc_eta H) _).
Qed.

Lemma AKcf_Initial_modmor'_step' {t u : Tmcf} (step : Tmcfσstep' t u) : AKcf_Initial_modmor' t = AKcf_Initial_modmor' u.
Proof.
  induction step.
  - refine (equal_f (kmm_substsubst H) (_,_,_)).
  - refine (equal_f (kmm_pi2snoc H) (_,_)).
  - refine (equal_f (kmm_substlam H) (_,_)).  
  - refine (equal_f (kmm_pi2_lin H) (_,_)).
  - refine (equal_f (kmm_substapp H) (_,_,_)).
Qed.

Fixpoint AKcf_Initial_mndmor'_step
  {δ σ : Tmscf} (step : δ --s> σ)
  : AKcf_Initial_mndmor' δ = AKcf_Initial_mndmor' σ
with AKcf_Initial_modmor'_step
  {x y : Tmcf} (step : x --> y)
  : AKcf_Initial_modmor' x = AKcf_Initial_modmor' y.
Proof.
{ induction step.
  all: try (cbn; do 2 f_equal; exact IHstep).
  - apply AKcf_Initial_mndmor'_step'.
    exact H0.
  - cbn.
    do 2 f_equal.
    apply AKcf_Initial_modmor'_step.
    exact H0. }
{ induction step.
  all: try (cbn; do 2 f_equal; exact IHstep).
  - apply (AKcf_Initial_modmor'_step' H0).
  - cbn; do 2 f_equal.
    apply AKcf_Initial_mndmor'_step.
    exact H0.
  - cbn.
    do 2 f_equal.
    apply AKcf_Initial_mndmor'_step.
    exact H0.
  - cbn.
    f_equal.
    apply IHstep. }
Qed.

Lemma AKcf_Initial_mndmor'_conv
  {δ σ : Tmscf} (step : δ --s>* σ)
  : AKcf_Initial_mndmor' δ = AKcf_Initial_mndmor' σ.
Proof.
  induction step.
  - by apply AKcf_Initial_mndmor'_step.
  - reflexivity.
  - by eapply eq_trans with (AKcf_Initial_mndmor' y).
Qed.

Lemma AKcf_Initial_modmor'_conv
{x y : Tmcf} (step : x -->* y)
: AKcf_Initial_modmor' x = AKcf_Initial_modmor' y.
Proof.
  induction step.
  - by apply AKcf_Initial_modmor'_step.
  - reflexivity.
  - by eapply eq_trans with (AKcf_Initial_modmor' y).
Qed.

Definition AKcf_Initial_mndmor
  := lift_fun1 TmscfσQ AKcf_Initial_mndmor'.

Lemma AKcf_Initial_mndmor_lift
  : {mono \pi : x / AKcf_Initial_mndmor' x >-> AKcf_Initial_mndmor x}.
Proof.
  unlock AKcf_Initial_mndmor => δ /=.
  rewrite [@pi]unlock [@repr]unlock; cbn.
  symmetry.
  apply AKcf_Initial_mndmor'_conv.
  apply nffun_conv.
Qed.

Canonical AKcf_Initial_mndmor_lift' := PiMono1 AKcf_Initial_mndmor_lift.

Definition AKcf_Initial_modmor
  := lift_fun1 TmcfσQ AKcf_Initial_modmor'.

Lemma AKcf_Initial_modmor_lift
  : {mono \pi : x / AKcf_Initial_modmor' x >-> AKcf_Initial_modmor x}.
Proof.
  unlock AKcf_Initial_modmor => x /=.
  rewrite [@pi]unlock [@repr]unlock; cbn.
  symmetry.
  apply AKcf_Initial_modmor'_conv.
  apply nffun_conv.
Qed.

Canonical AKcf_Initial_modmor_lift' := PiMono1 AKcf_Initial_modmor_lift.

Program Instance AKcf_Initial_mnd
  : MonoidMorphism (@kmm_mnd AKcf) (@kmm_mnd H)
  := {|
    mndmor := AKcf_Initial_mndmor
  |}.
Next Obligation.
  apply extensionality.
  intros [δ σ].
  rewrite /compose /=.
  rewrite -(reprK σ) -(reprK δ) !piE.
  reflexivity.
Qed.
Next Obligation.
  apply extensionality.
  intros [].
  rewrite /compose /=.
  rewrite !piE /=.
  reflexivity.
Qed.

Program Instance AKcf_Initial_mod
  : ModMorphism (@kmm_mod AKcf) (scalarRes AKcf_Initial_mnd H) := {|
    modmor := AKcf_Initial_modmor
  |}.
Next Obligation.
  apply extensionality.
  intros [t δ].
  rewrite /compose /Datatypes.id /=.
  rewrite -(reprK t) -(reprK δ) !piE.
  reflexivity.
Qed.

Program Instance AKcf_Initial'
  : KMMmorphism AKcf H
  := {|
    kmmor_mnd := AKcf_Initial_mnd;
    kmmor_mod := AKcf_Initial_mod;
  |}.
Next Obligation.
  apply extensionality.
  intros t.
  rewrite /compose /=.
  rewrite -(reprK t) !piE.
  f_equal.

  apply injective_projections;
  reflexivity.
Qed.

Program Instance AKcf_Initial
  : KMMλappMorphism AKcf H
  := {|
    KMMλapp_kmmmor := AKcf_Initial'
  |}.
Next Obligation.
apply extensionality.
intros [t u].
rewrite /compose /=.
rewrite -(reprK t) -(reprK u) !piE.
reflexivity.
Qed.
Next Obligation.
apply extensionality.
intros t.
rewrite /compose /=.
rewrite -(reprK t) !piE.
reflexivity.
Qed.

Lemma AKcf_kmm_id : kmm_id AKcf = \pi Tmscf_id.
Proof.
  apply subset_eq.
  cbn.
  by rewrite [@pi]unlock; cbn.
Qed.

Lemma AKcf_kmm_π1 {δ} : kmm_pi1 AKcf (\pi δ) = \pi_(TmscfσQ) (Tmscf_π₁ δ).
Proof.
  by rewrite /= /πM /compose /= piE.
Qed.

Lemma AKcf_kmm_π2 {δ} : kmm_pi2 AKcf (\pi δ) = \pi_(TmcfσQ) (Tmcf_π₂ δ).
Proof.
  by rewrite /= /πM /compose /= piE.
Qed.

Lemma AKcf_kmm_snoc {δ x} : kmm_snoc AKcf (\pi δ, \pi x) = \pi_(TmscfσQ) (Tmscf_snoc δ x).
Proof.
  by rewrite /= piE. 
Qed.

Lemma AKcf_kmm_app {x y} : @kmm_app AKcf (\pi x, \pi y) = \pi_(TmcfσQ) (Tmcf_app x y).
Proof.
  by rewrite /= piE. 
Qed.

Lemma AKcf_kmm_lam {x} : @kmm_lam AKcf (\pi x) = \pi_(TmcfσQ) (Tmcf_lam x).
Proof.
  by rewrite /= piE. 
Qed.

Fixpoint AKcf_Initial_mnd_uniqueness'
  (F : KMMλappMorphism AKcf H) (δ : Tmscf) (δV: Tmscfσvalue δ) {struct δ}
  : @mndmor _ _ (@ kmmor_mnd _ _ F) (\pi δ)
  =  AKcf_Initial_mndmor' δ
with AKcf_Initial_mod_uniqueness'
(F : KMMλappMorphism AKcf H) (x : Tmcf) (xV: Tmcfσvalue x) {struct x}
: @modmor _ _ _ (@kmmor_mod _ _ F) (\pi x)
=  AKcf_Initial_modmor' x.
Proof.
{ induction δV using Tmscfσvalue_rect.
  { induction H0 using cf_iter_π₁idP_rec.
    - rewrite -AKcf_kmm_id.
      apply (equal_f mndmor_unit tt).
    - rewrite -AKcf_kmm_π1.
      eapply eq_trans.
      { apply (equal_f (kmmor_coherence_pi1 F)). }
      rewrite /= /compose.
      do 2 f_equal.
      exact IHcf_iter_π₁idP. }
  - specialize (AKcf_Initial_mod_uniqueness' F y H0) as IHxV.
    rewrite -AKcf_kmm_snoc.
    eapply eq_trans.
    { apply (equal_f (kmmor_coherence_snoc F) (_,_)). }
    rewrite /= /compose /bimap.
    f_equal.
    apply /injective_projections.
    - exact IHδV.
    - exact IHxV.    
}
{ induction xV using Tmcfσvalue_rect.
  - specialize (AKcf_Initial_mnd_uniqueness' F δ (Tmscfσvalue_iterπ₁id H0)) as IHδV.
    rewrite -AKcf_kmm_π2.
    eapply eq_trans.
    { apply (equal_f (kmmor_coherence_pi2 F)). }
    rewrite /= /compose.
    do 2 f_equal.
    exact IHδV.
  - rewrite -AKcf_kmm_app.
    eapply eq_trans.
    { apply (equal_f (@KMMλapp_appcoh _ _ F)). }
    rewrite /compose /=.
    f_equal.
    apply /injective_projections.
    - exact IHxV1.
    - exact IHxV2.
  - rewrite -AKcf_kmm_lam.
    eapply eq_trans.
    { apply (equal_f (@KMMλapp_lamcoh _ _ F)). }
    rewrite /compose /=.
    f_equal.
    exact IHxV. 
}
Qed.

Lemma AKcf_Initial_mnd_uniqueness (F : KMMλappMorphism AKcf H)
  : @mndmor _ _ (@ kmmor_mnd _ _ F) = @mndmor _ _ (@ kmmor_mnd _ _ AKcf_Initial).
Proof.
  apply extensionality.
  intro x.
  rewrite /= -(reprK x) !piE.
  rewrite [@repr]unlock; cbn.
  apply AKcf_Initial_mnd_uniqueness'.
  apply Tmscfσnf_is_value.
  destruct x as [x isnf].
  apply isnf.
Qed.

Lemma AKcf_Initial_mod_uniqueness (F : KMMλappMorphism AKcf H)
  : @modmor _ _ _ (@ kmmor_mod _ _ F) = @modmor _ _ _ (@ kmmor_mod _ _ AKcf_Initial).
Proof.
  apply extensionality.
  intro x.
  rewrite /= -(reprK x) !piE.
  rewrite [@repr]unlock; cbn.
  apply AKcf_Initial_mod_uniqueness'.
  apply Tmcfσnf_is_value.
  destruct x as [x isnf].
  apply isnf.
Qed.

Lemma AKcf_Initial_kmm_uniqueness (F : KMMλappMorphism AKcf H)
 : @KMMλapp_kmmmor _ _ F = @KMMλapp_kmmmor _ _ AKcf_Initial.
Proof.
  apply KMMmorphism_eq.
  - apply AKcf_Initial_mnd_uniqueness.
  - apply AKcf_Initial_mod_uniqueness.
Qed.

Lemma AKcf_Initial_uniqueness (F : KMMλappMorphism AKcf H) : F = AKcf_Initial.
Proof.
  apply KMMλappMorphism_eq.
  apply AKcf_Initial_kmm_uniqueness.
Qed.

Check AKcf_Initial_uniqueness.

End Initiality.