From CwFdeBruijn.Syntax.Setup Require Export Setup GenRewr RelationsLemmas.
Require Import Setoid Morphisms RelationClasses.
From CwFdeBruijn.Syntax.AKcf Require Import AKcf AKcf_Conv.

Notation "'id'" := (Tmscf_id) (at level 5) : AKcf.
Notation "'⟨' δ ',' a '⟩'" := (Tmscf_snoc δ a) (δ at level 40, a at level 40) : AKcf.
Notation "δ₁ '○' δ₂" := (Tmscf_comp δ₁ δ₂) (at level 9) : AKcf.
Notation "'π1' δ" := (Tmscf_π₁ δ) (at level 40)  : AKcf.
Notation "a '@' b" := (Tmcf_app a b) (at level 9)  : AKcf.
Notation "a '[' δ ']'" := (Tmcf_subst a δ) : AKcf.
Notation "'λ' a" := (Tmcf_lam a) (at level 40)  : AKcf.
Notation "'π2' a" := (Tmcf_π₂ a) (at level 40)  : AKcf.

Section GeneralizedRewriting.

Global Instance Tmscf_σstep'_σstep_subrelation : subrelation Tmscfσstep' Tmscfσstep.
Proof. intros ? ?. apply cf_srefl. Qed.
Global Instance Tmscf_σstep_σconv_subrelation : subrelation Tmscfσstep Tmscfσconv.
Proof. apply rt_subrelation. Qed.
Global Instance Tmscf_σconv_σeq_subrelation : subrelation Tmscfσconv Tmscfσeq.
Proof. apply clos_rt_clos_rst. Qed.

Global Instance Tmscf_σstep_σeq_subrelation : subrelation Tmscfσstep Tmscfσeq.
Proof. apply rst_subrelation. Qed.
Global Instance Tmscf_σstep'_σconv_subrelation : subrelation Tmscfσstep' Tmscfσconv.
Proof.
  intros ? ? ?.
  apply rt_subrelation.
  apply cf_srefl.
  exact H.
Qed.
Global Instance Tmscf_σstep'_σeq_subrelation : subrelation Tmscfσstep' Tmscfσeq.
Proof.
  etransitivity.
  - apply Tmscf_σstep'_σconv_subrelation.
  - apply _.
Qed.

Global Instance Tmcf_σstep'_σstep_subrelation : subrelation Tmcfσstep' Tmcfσstep.
Proof. intros ? ?. apply cf_refl. Qed.
Global Instance Tmcf_σstep_σconv_subrelation : subrelation Tmcfσstep Tmcfσconv.
Proof. apply rt_subrelation. Qed.
Global Instance Tmcf_σconv_σeq_subrelation : subrelation Tmcfσconv Tmcfσeq.
Proof. apply clos_rt_clos_rst. Qed.

Global Instance Tmcf_σstep_σeq_subrelation : subrelation Tmcfσstep Tmcfσeq.
Proof. apply rst_subrelation. Qed.
Global Instance Tmcf_σstep'_σconv_subrelation : subrelation Tmcfσstep' Tmcfσconv.
Proof.
  intros ? ? ?.
  apply rt_subrelation.
  apply cf_refl.
  exact H.
Qed.
Global Instance Tmcf_σstep'_σeq_subrelation : subrelation Tmcfσstep' Tmcfσeq.
Proof.
  etransitivity.
  - apply Tmcf_σstep'_σconv_subrelation.
  - apply _.
Qed.

(* Compatibility instances *)

Global Instance Tmscf_snoc_σstep_eq_σconv : Proper (Tmscfσstep ==> eq ==> Tmscfσconv) Tmscf_snoc.
Proof. intros ? ? H ? ? []; apply rt_step; apply (snoc_Tmscf_prpg _ _ H). Qed.
Global Instance Tmscf_snoc_eq_σstep_σconv : Proper (eq ==> Tmcfσstep ==> Tmscfσconv) Tmscf_snoc.
Proof. intros ? ? [] ? ? H; apply rt_step; apply (snoc_Tmcf_prpg _ _ H). Qed.
Global Instance Tmscf_snoc_σconv : Proper (Tmscfσconv ==> Tmcfσconv ==> Tmscfσconv) Tmscf_snoc.
Proof. apply rt_lift_proper_2; apply _. Qed.

Global Instance Tmscf_comp_σstep_σrefl_σconv : Proper (Tmscfσstep ==> eq ==> Tmscfσconv) Tmscf_comp.
Proof. intros ? ? H ? ? []; apply rt_step; apply (cf_compl_prpg _ _ H). Qed.
Global Instance Tmscf_comp_σrefl_σstep_σconv : Proper (eq ==> Tmscfσstep ==> Tmscfσconv) Tmscf_comp.
Proof. intros ? ? [] ? ? H; apply rt_step; apply (cf_compr_prpg _ _ H). Qed.
Global Instance Tmscf_comp_σconv : Proper (Tmscfσconv ==> Tmscfσconv ==> Tmscfσconv) Tmscf_comp.
Proof. apply rt_lift_proper_2; apply _. Qed.

Global Instance Tmcf_app_σstep_σrefl_σconv : Proper (Tmcfσstep ==> eq ==> Tmcfσconv) Tmcf_app.
Proof. intros ? ? H ? ? []; apply rt_step; apply (cf_rand_prpg _ _ H). Qed.
Global Instance Tmcf_app_σrefl_σstep_σconv : Proper (eq ==> Tmcfσstep ==> Tmcfσconv) Tmcf_app.
Proof. intros ? ? [] ? ? H; apply rt_step; apply (cf_rator_prpg _ _ H). Qed.
Global Instance Tmcf_app_σconv : Proper (Tmcfσconv ==> Tmcfσconv ==> Tmcfσconv) Tmcf_app.
Proof. apply rt_lift_proper_2; apply _. Qed.

Global Instance Tmcf_subst_σstep_σrefl_σconv : Proper (Tmcfσstep ==> eq ==> Tmcfσconv) Tmcf_subst.
Proof. intros ? ? H ? ? []; apply rt_step; apply (subst_Tmcf_prpg _ _ H). Qed.
Global Instance Tmcf_subst_σrefl_σstep_σconv : Proper (eq ==> Tmscfσstep ==> Tmcfσconv) Tmcf_subst.
Proof. intros ? ? [] ? ? H; apply rt_step; apply (subst_Tmscf_prpg _ _ H). Qed.
Global Instance Tmcf_subst_σconv : Proper (Tmcfσconv ==> Tmscfσconv ==> Tmcfσconv) Tmcf_subst.
Proof. apply rt_lift_proper_2; apply _. Qed.

Global Instance Tmscf_lam_σstep_σconv : Proper (Tmcfσstep ==> Tmcfσconv) Tmcf_lam.
Proof. intros ? ? H; apply rt_step; apply (cf_lam_prpg _ _ H). Qed.
Global Instance Tmscf_lam_σconv : Proper (Tmcfσconv ==> Tmcfσconv) Tmcf_lam.
Proof. apply rt_lift_proper_1; apply _. Qed.

Global Instance Tmscf_lift_σstep_σconv : Proper (Tmscfσstep ==> Tmscfσconv) lift.
Proof. unfold lift; intros ? ? H; now rewrite H. Qed.
Global Instance Tmscf_lift_σconv : Proper (Tmscfσconv ==> Tmscfσconv) lift.
Proof. apply rt_lift_proper_1; apply _. Qed.

Global Instance Tmscf_π₁_σstep_σconv : Proper (Tmscfσstep ==> Tmscfσconv) Tmscf_π₁.
Proof. intros ? ? H; apply rt_step; apply (cf_π₁_prpg _ _ H). Qed.
Global Instance Tmscf_π₁_σconv : Proper (Tmscfσconv ==> Tmscfσconv) Tmscf_π₁.
Proof. apply rt_lift_proper_1; apply _. Qed.

Global Instance Tmcf_π₂_σstep_σconv : Proper (Tmscfσstep ==> Tmcfσconv) Tmcf_π₂.
Proof. intros ? ? H; apply rt_step; apply (cf_π₂_prpg _ _ H). Qed.
Global Instance Tmcf_π₂_σconv : Proper (Tmscfσconv ==> Tmcfσconv) Tmcf_π₂.
Proof. apply rt_lift_proper_1; apply _. Qed.

Global Instance cf_iter_π₁_σstep_σconv {i} : Proper (Tmscfσstep ==> Tmscfσconv) (cf_iter_π₁ i).
Proof. intros ? ? H.  apply rt_step. apply (AKcfσstep_iter_π₁_compatibility _ _ H). Qed.
Global Instance cf_iter_π₁_σconv {i} : Proper (Tmscfσconv ==> Tmscfσconv) (cf_iter_π₁ i).
Proof. intros ? ? ?. apply AKcfσconv_iter_π₁_compatibility. exact H. Qed.

Global Instance cf_iter_π₂_σstep_σconv {i} : Proper (Tmscfσstep ==> Tmcfσconv) (cf_iter_π₂ i).
Proof. intros ? ? H.  apply rt_step. apply (AKcfσstep_iter_π₂_compatibility _ _ H). Qed.
Global Instance cf_iter_π₂_σconv {i} : Proper (Tmscfσconv ==> Tmcfσconv) (cf_iter_π₂ i).
Proof. intros ? ? ?. apply AKcfσconv_iter_π₂_compatibility. exact H. Qed.

(* Instances for σeq *)
Instance Proper_R_eq_Tmscfσeq {A B : Type} {R: relation A}
  (f : A -> B -> Tmscf)
  `{Hf : Proper _ (R ==> eq ==> Tmscfσconv) f} :
  Proper (R ==> eq ==> Tmscfσeq) f.
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  apply (clos_rt_clos_rst _ Tmscfσstep).
  apply (Hf _ _ Hx _ _ Hy).
Qed.
Instance Proper_eq_R_Tmscfσeq {A B : Type} {R: relation B}
  (f : A -> B -> Tmscf)
  `{Hf : Proper _ (eq ==> R ==> Tmscfσconv) f} :
  Proper (eq ==> R ==> Tmscfσeq) f.
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  apply (clos_rt_clos_rst _ Tmscfσstep).
  apply (Hf _ _ Hx _ _ Hy).
Qed.
Instance Proper_R_eq_TmASσeq {A B : Type} {R: relation A}
  (f : A -> B -> Tmcf)
  `{Hf : Proper _ (R ==> eq ==> Tmcfσconv) f} :
  Proper (R ==> eq ==> Tmcfσeq) f.
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  apply (clos_rt_clos_rst _ Tmcfσstep).
  apply (Hf _ _ Hx _ _ Hy).
Qed.
Instance Proper_eq_R_Tmcfσeq {A B : Type} {R: relation B}
  (f : A -> B -> Tmcf)
  `{Hf : Proper _ (eq ==> R ==> Tmcfσconv) f} :
  Proper (eq ==> R ==> Tmcfσeq) f.
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  apply (clos_rt_clos_rst _ Tmcfσstep).
  apply (Hf _ _ Hx _ _ Hy).
Qed.

Instance Proper_R_Tmscfσeq {A : Type} {R: relation A}
  (f : A -> Tmscf)
  `{Hf : Proper _ (R ==> Tmscfσconv) f} :
  Proper (R ==> Tmscfσeq) f.
Proof.
  intros x1 x2 Hx.
  apply (clos_rt_clos_rst _ Tmscfσstep).
  apply (Hf _ _ Hx).
Qed.
Instance Proper_R_Tmcfσeq {A : Type} {R: relation A}
  (f : A -> Tmcf)
  `{Hf : Proper _ (R ==> Tmcfσconv) f} :
  Proper (R ==> Tmcfσeq) f.
Proof.
  intros x1 x2 Hx.
  apply (clos_rt_clos_rst _ Tmcfσstep).
  apply (Hf _ _ Hx).
Qed.

Global Instance Tmscf_snoc_σeq : Proper (Tmscfσeq ==> Tmcfσeq ==> Tmscfσeq) Tmscf_snoc.
Proof. apply rst_lift_proper_2; apply _. Qed.
Global Instance Tmscf_comp_σeq : Proper (Tmscfσeq ==> Tmscfσeq ==> Tmscfσeq) Tmscf_comp.
Proof. apply rst_lift_proper_2; apply _. Qed.
Global Instance Tmcf_app_σeq : Proper (Tmcfσeq ==> Tmcfσeq ==> Tmcfσeq) Tmcf_app.
Proof. apply rst_lift_proper_2; apply _. Qed.
Global Instance Tmcf_subst_σeq : Proper (Tmcfσeq ==> Tmscfσeq ==> Tmcfσeq) Tmcf_subst.
Proof. apply rst_lift_proper_2; apply _. Qed.
Global Instance Tmscf_lam_σeq : Proper (Tmcfσeq ==> Tmcfσeq) Tmcf_lam.
Proof. apply rst_lift_proper_1. apply _. Qed.
Global Instance Tmscf_π₁_σeq : Proper (Tmscfσeq ==> Tmscfσeq) Tmscf_π₁.
Proof. apply rst_lift_proper_1. apply _. Qed.
Global Instance Tmcf_π₂_σeq : Proper (Tmscfσeq ==> Tmcfσeq) Tmcf_π₂.
Proof. apply rst_lift_proper_1. apply _. Qed.

Global Instance Tmscf_lift_σstep_σeq : Proper (Tmscfσstep ==> Tmscfσeq) lift.
Proof. unfold lift; intros ? ? H; now rewrite H. Qed.
Global Instance Tmscf_lift_σeq : Proper (Tmscfσeq ==> Tmscfσeq) lift.
Proof. apply rst_lift_proper_1; apply _. Qed.

End GeneralizedRewriting.

Close Scope AKcf.