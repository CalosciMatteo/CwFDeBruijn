From CwFdeBruijn.Syntax.AKcf Require Export AKcf occur.
From CwFdeBruijn.Syntax.Setup Require Import RelationsLemmas. 
Declare Scope AKcf.
Delimit Scope AKcf with AKcf.
Open Scope AKcf.

Inductive toTmscf_compatible (R : relation Tmcf) (Rs : relation (Tmscf)) : relation (Tmscf) :=
  | cf_srefl {δ' δ : Tmscf}
    : Rs δ' δ -> toTmscf_compatible R Rs δ' δ
  | snoc_Tmscf_prpg {δ' δ : Tmscf} {x : Tmcf}
    : toTmscf_compatible R Rs δ' δ -> toTmscf_compatible R Rs (Tmscf_snoc δ' x) (Tmscf_snoc δ x)
  | snoc_Tmcf_prpg {x' x : Tmcf} {δ : Tmscf}
    : toTmcf_compatible R Rs x' x -> toTmscf_compatible R Rs (Tmscf_snoc δ x') (Tmscf_snoc δ x)
  | cf_compl_prpg {δ' δ : Tmscf} {σ : Tmscf}
    : toTmscf_compatible R Rs δ' δ -> toTmscf_compatible R Rs (Tmscf_comp δ' σ) (Tmscf_comp δ σ)
  | cf_compr_prpg {σ' σ : Tmscf} {δ : Tmscf}
    : toTmscf_compatible R Rs σ' σ -> toTmscf_compatible R Rs (Tmscf_comp δ σ') (Tmscf_comp δ σ)
  | cf_π₁_prpg {δ' δ : Tmscf}
    : toTmscf_compatible R Rs δ' δ -> toTmscf_compatible R Rs (Tmscf_π₁ δ') (Tmscf_π₁ δ)
with toTmcf_compatible (R : relation (Tmcf)) (Rs : relation (Tmscf)): relation (Tmcf) :=
  | cf_refl {x' x : Tmcf}
    : R x' x
    -> toTmcf_compatible R Rs x' x
  | subst_Tmcf_prpg {x' x : Tmcf} {δ : Tmscf}
    : toTmcf_compatible R Rs x' x ->
      toTmcf_compatible R Rs (Tmcf_subst x' δ) (Tmcf_subst x δ)
  | subst_Tmscf_prpg {δ' δ : Tmscf} {x : Tmcf}
    : toTmscf_compatible R Rs δ' δ ->
      toTmcf_compatible R Rs (Tmcf_subst x δ') (Tmcf_subst x δ)
  | cf_π₂_prpg {δ' δ : Tmscf}
    : toTmscf_compatible R Rs δ' δ ->
      toTmcf_compatible R Rs (Tmcf_π₂ δ') (Tmcf_π₂ δ)
  | cf_rand_prpg {x' x y: Tmcf}
    : toTmcf_compatible R Rs x' x ->
      toTmcf_compatible R Rs (Tmcf_app x' y) (Tmcf_app x y)
  | cf_rator_prpg {x y' y : Tmcf}
    : toTmcf_compatible R Rs y' y ->
      toTmcf_compatible R Rs (Tmcf_app x y') (Tmcf_app x y)
  | cf_lam_prpg {x' x : Tmcf}
    : toTmcf_compatible R Rs x' x ->
      toTmcf_compatible R Rs (Tmcf_lam x') (Tmcf_lam x).

Ltac onestep := apply rt_step; try apply cf_refl; try apply cf_srefl.

Inductive Tmscfλstep' : relation (Tmscf) := .

Inductive Tmcfλstep' : relation (Tmcf) :=
  | Tmcf_beta {t x : Tmcf}
    : Tmcfλstep'
      (Tmcf_app (Tmcf_lam t) x)
      (Tmcf_subst t (Tmscf_snoc Tmscf_id x))
  | Tmcf_eta {t : Tmcf}
    : Tmcfλstep'
      (Tmcf_lam (Tmcf_app
        (Tmcf_subst t (Tmscf_π₁ Tmscf_id))
        (Tmcf_π₂ Tmscf_id)))
      t.

Definition Tmscfλstep := toTmscf_compatible Tmcfλstep' Tmscfλstep'.
Notation " δ '⩶s>' δ' " := (Tmscfλstep δ δ') (at level 55, δ' at level 55) : AKcf.

Definition Tmcfλstep := toTmcf_compatible Tmcfλstep' Tmscfλstep'.
Notation " x '⩶>' x' " := (Tmcfλstep x x') (at level 55, x' at level 55) : AKcf.

Definition Tmcfλconv := clos_refl_trans (Tmcf) (Tmcfλstep).
Notation " x '⩶>*' x' " := (Tmcfλconv x x') (at level 55, x' at level 55) : AKcf.

Definition Tmscfλconv := clos_refl_trans (Tmscf) (Tmscfλstep).
Notation " x '⩶s>*' x' " := (Tmscfλconv x x') (at level 55, x' at level 55) : AKcf.

Definition Tmcfλeq := clos_refl_sym_trans (Tmcf) (Tmcfλstep).
Notation " x '<⩶>*' x' " := (Tmcfλeq x x') (at level 55, x' at level 55) : AKcf.

Definition Tmscfλeq := clos_refl_sym_trans (Tmscf) (Tmscfλstep).
Notation " x '<⩶s>*' x' " := (Tmscfλeq x x') (at level 55, x' at level 55) : AKcf.


Inductive Tmscfσstep' : relation (Tmscf) :=
  | cf_idl {δ : Tmscf}
    : Tmscfσstep' (Tmscf_comp (Tmscf_id) δ) δ
  | cf_idr {δ : Tmscf}
    : Tmscfσstep' (Tmscf_comp δ (Tmscf_id)) δ
  | cf_ass {σ : Tmscf} {δ : Tmscf} {ν : Tmscf}
    : Tmscfσstep' (Tmscf_comp (Tmscf_comp σ δ) ν) (Tmscf_comp σ (Tmscf_comp δ ν))
  | cf_snocomp {δ : Tmscf} {t : Tmcf} {σ : Tmscf}
    : Tmscfσstep' (Tmscf_comp (Tmscf_snoc δ t) σ) (Tmscf_snoc (Tmscf_comp δ σ) (Tmcf_subst t σ))
  | cf_π₁beta {δ : Tmscf} {t : Tmcf}
    : Tmscfσstep' (Tmscf_π₁ (Tmscf_snoc δ t)) δ
  | cf_π₁comp {δ σ : Tmscf}
    : Tmscfσstep' (Tmscf_comp (Tmscf_π₁ δ) σ) (Tmscf_π₁ (Tmscf_comp δ σ))
  | cf_πeta {δ : Tmscf} : Tmscfσstep' (Tmscf_snoc (Tmscf_π₁ δ) (Tmcf_π₂ δ)) δ.

Inductive Tmcfσstep' : relation (Tmcf) :=
  | cf_substsubst {σ : Tmscf} {δ : Tmscf} {t : Tmcf}
    : Tmcfσstep' (Tmcf_subst (Tmcf_subst t δ) σ) (Tmcf_subst t (Tmscf_comp δ σ))
  | cf_π₂beta {δ : Tmscf} {t : Tmcf}
    : Tmcfσstep' (Tmcf_π₂ (Tmscf_snoc δ t)) t
  | cf_lamsubst {δ : Tmscf} {t : Tmcf}
    : Tmcfσstep' (Tmcf_subst (Tmcf_lam t) δ) (Tmcf_lam (Tmcf_subst t (lift δ)))
  | cf_substπ₂ {δ σ : Tmscf}
    : Tmcfσstep' (Tmcf_subst (Tmcf_π₂ σ) δ) (Tmcf_π₂ (Tmscf_comp σ δ))
  | cf_appsubst {x y: Tmcf} {δ: Tmscf}
    : Tmcfσstep' (Tmcf_subst (Tmcf_app x y) δ)
        (Tmcf_app (Tmcf_subst x δ) (Tmcf_subst y δ)).

Definition Tmscfσstep := toTmscf_compatible Tmcfσstep' Tmscfσstep'.
Notation " δ '--s>' δ' " := (Tmscfσstep δ δ') (at level 55, δ' at level 55) : AKcf.

Definition Tmcfσstep := toTmcf_compatible Tmcfσstep' Tmscfσstep'.
Notation " x '-->' x' " := (Tmcfσstep x x') (at level 55, x' at level 55): AKcf.

Definition Tmcfσconv := clos_refl_trans (Tmcf) (Tmcfσstep).
Notation " x '-->*' x' " := (Tmcfσconv x x') (at level 55, x' at level 55) : AKcf.

Definition Tmscfσconv := clos_refl_trans (Tmscf) (Tmscfσstep).
Notation " x '--s>*' x' " := (Tmscfσconv x x') (at level 55, x' at level 55) : AKcf.

Definition Tmcfσeq := clos_refl_sym_trans (Tmcf) (Tmcfσstep).
Notation " x '<-->*' x' " := (Tmcfσeq x x') (at level 55, x' at level 55) : AKcf.

Definition Tmscfσeq := clos_refl_sym_trans (Tmscf) (Tmscfσstep).
Notation " x '<--s>*' x' " := (Tmscfσeq x x') (at level 55, x' at level 55) : AKcf.

Record AKcf_compatible (R : Tmcf -> Tmcf -> Prop) (Rs : Tmscf -> Tmscf -> Prop) := make_AKcf_compatible {
  snoc_Tmscf_step_compatibility {δ' δ : Tmscf} {x : Tmcf}
    : Rs δ' δ -> Rs (Tmscf_snoc δ' x) (Tmscf_snoc δ x);
  snoc_Tmcf_step_compatibility {x' x : Tmcf} {δ : Tmscf}
    : R x' x -> Rs (Tmscf_snoc δ x') (Tmscf_snoc δ x);
  cf_compl_step_compatibility {δ' δ : Tmscf} {σ : Tmscf}
    : Rs δ' δ -> Rs (Tmscf_comp δ' σ) (Tmscf_comp δ σ);
  cf_compr_step_compatibility {σ' σ : Tmscf} {δ : Tmscf}
    : Rs σ' σ -> Rs (Tmscf_comp δ σ') (Tmscf_comp δ σ);
  cf_π₁_step_compatibility {δ' δ : Tmscf}
    : Rs δ' δ -> Rs (Tmscf_π₁ δ') (Tmscf_π₁ δ);
  subst_Tmcf_step_compatibility {x' x : Tmcf} {δ : Tmscf}
    : R x' x -> R (Tmcf_subst x' δ) (Tmcf_subst x δ);
  subst_Tmscf_step_compatibility {δ' δ : Tmscf} {x : Tmcf}
    : Rs δ' δ -> R (Tmcf_subst x δ') (Tmcf_subst x δ);
  cf_π₂_step_compatibility {δ' δ : Tmscf}
    : Rs δ' δ -> R (Tmcf_π₂ δ') (Tmcf_π₂ δ);
  cf_rator_step_compatibility {x' x y : Tmcf}
    : R x' x -> R (Tmcf_app x' y) (Tmcf_app x y);
  cf_rand_step_compatibility {x y' y : Tmcf}
    : R y' y -> R (Tmcf_app x y') (Tmcf_app x y);
  cf_lam_step_compatibility {x' x : Tmcf}
    : R x' x -> R (Tmcf_lam x') (Tmcf_lam x);
}.

Lemma cf_iter_π₁_compatibility
  (R : Tmcf -> Tmcf -> Prop) (Rs : Tmscf -> Tmscf -> Prop)
  (H : AKcf_compatible R Rs)
  {δ' δ : Tmscf} {i : nat}
  : Rs δ' δ -> Rs (cf_iter_π₁ i δ') (cf_iter_π₁ i δ).
Proof.
  intro Rδ.
  induction i.
  - exact Rδ.
  - cbn.
    apply (cf_π₁_step_compatibility R Rs H).
    exact IHi.
Qed.

Lemma cf_iter_π₂_compatibility
  (R : Tmcf -> Tmcf -> Prop) (Rs : Tmscf -> Tmscf -> Prop)
  (H : AKcf_compatible R Rs)
  {δ' δ : Tmscf} {i : nat}
  : Rs δ' δ -> R (cf_iter_π₂ i δ') (cf_iter_π₂ i δ).
Proof.
  intro Rδ.
  unfold cf_iter_π₂.
  apply (cf_π₂_step_compatibility R Rs H).
  apply (cf_iter_π₁_compatibility R Rs H).
  exact Rδ.
Qed.

Lemma cf_app_parallelcompatibility
  (R : Tmcf -> Tmcf -> Prop) (Rs : Tmscf -> Tmscf -> Prop)
  (trans_R : RelationClasses.Transitive R)
  (H : AKcf_compatible R Rs)
  {x x' y y'}
  : R x' x -> R y' y -> R (Tmcf_app x' y') (Tmcf_app x y).
Proof.
  intros red_x red_y.
  eapply trans_R.
  - eapply (cf_rator_step_compatibility _ _ H).
    exact red_x.
  - eapply (cf_rand_step_compatibility _ _ H).
    exact red_y.
Qed.

Lemma cf_comp_parallelcompatibility
  (R : Tmcf -> Tmcf -> Prop) (Rs : Tmscf -> Tmscf -> Prop)
  (trans_Rs : Relation_Definitions.transitive _ Rs)
  (H : AKcf_compatible R Rs)
  {x x' y y'}
  : Rs x' x -> Rs y' y -> Rs (Tmscf_comp x' y') (Tmscf_comp x y).
Proof.
  intros red_x red_y.
  eapply trans_Rs.
  - eapply (cf_compl_step_compatibility _ _ H).
    exact red_x.
  - eapply (cf_compr_step_compatibility _ _ H).
    exact red_y.
Qed.

Lemma cf_subst_parallelcompatibility
  (R : Tmcf -> Tmcf -> Prop) (Rs : Tmscf -> Tmscf -> Prop)
  (trans_R : Relation_Definitions.transitive _ R)
  (trans_Rs : Relation_Definitions.transitive _ Rs)
  (H : AKcf_compatible R Rs)
  {x x' y y'}
  : R x' x -> Rs y' y -> R (Tmcf_subst x' y') (Tmcf_subst x y).
Proof.
  intros red_x red_y.
  eapply trans_R.
  - eapply (subst_Tmcf_step_compatibility _ _ H).
    exact red_x.
  - eapply (subst_Tmscf_step_compatibility _ _ H).
    exact red_y.
Qed.

Lemma cf_snoc_parallelcompatibility
  (R : Tmcf -> Tmcf -> Prop) (Rs : Tmscf -> Tmscf -> Prop)
  (trans_R : Relation_Definitions.transitive _ R)
  (trans_Rs : Relation_Definitions.transitive _ Rs)
  (H : AKcf_compatible R Rs)
  {x x' y y'}
  : Rs x' x -> R y' y -> Rs (Tmscf_snoc x' y') (Tmscf_snoc x y).
Proof.
  intros red_x red_y.
  eapply trans_Rs.
  - eapply (snoc_Tmcf_step_compatibility _ _ H).
    exact red_y.
  - eapply (snoc_Tmscf_step_compatibility _ _ H).
    exact red_x.
Qed.

Create HintDb AKcf.
#[export] Hint Unfold Tmcfλstep : AKcf.
#[export] Hint Unfold Tmcfλconv : AKcf.
#[export] Hint Unfold Tmcfλeq : AKcf.
#[export] Hint Unfold Tmscfλstep : AKcf.
#[export] Hint Unfold Tmscfλconv : AKcf.
#[export] Hint Unfold Tmscfλeq : AKcf.
#[export] Hint Unfold Tmcfσstep : AKcf.
#[export] Hint Unfold Tmcfσconv : AKcf.
#[export] Hint Unfold Tmcfσeq : AKcf.
#[export] Hint Unfold Tmscfσstep : AKcf.
#[export] Hint Unfold Tmscfσconv : AKcf.
#[export] Hint Unfold Tmscfσeq : AKcf.
#[export] Hint Constructors Tmscfλstep' : AKcf.
#[export] Hint Constructors Tmcfλstep' : AKcf.
#[export] Hint Constructors toTmscf_compatible Tmcfλstep' Tmscfλstep' : AKcf.
#[export] Hint Constructors toTmcf_compatible Tmcfλstep' Tmscfλstep' : AKcf.
#[export] Hint Constructors Tmscfσstep' : AKcf.
#[export] Hint Constructors Tmcfσstep' : AKcf.
#[export] Hint Constructors toTmscf_compatible Tmcfσstep' Tmscfσstep' : AKcf.
#[export] Hint Constructors toTmcf_compatible Tmcfσstep' Tmscfσstep' : AKcf.

Theorem AKcfλstep_compatibility : AKcf_compatible (Tmcfλstep) (Tmscfλstep).
Proof.
  apply make_AKcf_compatible; auto with AKcf.
Qed.

Theorem AKcfλconv_compatibility : AKcf_compatible (Tmcfλconv) (Tmscfλconv).
Proof.
  apply make_AKcf_compatible; intros.
  all: try
    (apply (rt_compatibility Tmscfλstep Tmscfλstep)) ||
    (apply (rt_compatibility Tmcfλstep Tmscfλstep)) ||
    (apply (rt_compatibility Tmcfλstep Tmcfλstep)) ||
    (apply (rt_compatibility Tmscfλstep Tmcfλstep)).
  all: auto with AKcf sets.
  + apply (rt_compatibility Tmscfλstep Tmscfλstep (fun δ => Tmscf_snoc δ x)); auto with AKcf sets.
  + apply (rt_compatibility Tmscfλstep Tmscfλstep (fun δ => Tmscf_comp δ σ)); auto with AKcf sets.
  + apply (rt_compatibility Tmcfλstep Tmcfλstep (fun x => Tmcf_subst x δ)); auto with AKcf sets.
  + apply (rt_compatibility Tmcfλstep Tmcfλstep (fun x => Tmcf_app x y)); auto with AKcf sets.
Qed.

Theorem AKcfλeq_compatibility : AKcf_compatible (Tmcfλeq) (Tmscfλeq).
Proof.
  apply make_AKcf_compatible; intros.
  all: try
    (apply (rst_compatibility Tmscfλstep Tmscfλstep)) ||
    (apply (rst_compatibility Tmcfλstep Tmscfλstep)) ||
    (apply (rst_compatibility Tmcfλstep Tmcfλstep)) ||
    (apply (rst_compatibility Tmscfλstep Tmcfλstep)).
  all: auto with AKcf sets.
  + apply (rst_compatibility Tmscfλstep Tmscfλstep (fun δ => Tmscf_snoc δ x)); auto with AKcf sets.
  + apply (rst_compatibility Tmscfλstep Tmscfλstep (fun δ => Tmscf_comp δ σ)); auto with AKcf sets.
  + apply (rst_compatibility Tmcfλstep Tmcfλstep (fun x => Tmcf_subst x δ)); auto with AKcf sets.
  + apply (rst_compatibility Tmcfλstep Tmcfλstep (fun x => Tmcf_app x y)); auto with AKcf sets.
Qed.

Theorem AKcfσstep_compatibility : AKcf_compatible (Tmcfσstep) (Tmscfσstep).
Proof.
  apply make_AKcf_compatible; auto with AKcf.
Qed.

Lemma AKcfσstep_iter_π₁_compatibility (δ σ: Tmscf) (H: δ --s> σ) (i: nat): cf_iter_π₁ i δ --s> cf_iter_π₁ i σ.
Proof.
  apply (cf_iter_π₁_compatibility Tmcfσstep Tmscfσstep).
  - apply AKcfσstep_compatibility.
  - exact H.
Qed.

Lemma AKcfσstep_iter_π₂_compatibility (δ σ: Tmscf) (H: δ --s> σ) (i: nat): cf_iter_π₂ i δ --> cf_iter_π₂ i σ.
Proof.
  unfold cf_iter_π₂.
  apply (cf_π₂_step_compatibility Tmcfσstep Tmscfσstep).
  { apply AKcfσstep_compatibility. }
  apply AKcfσstep_iter_π₁_compatibility.
  exact H.
Qed.

Theorem AKcfσconv_compatibility : AKcf_compatible (Tmcfσconv) (Tmscfσconv).
Proof.
  apply make_AKcf_compatible; intros.
  all: try
    (apply (rt_compatibility Tmscfσstep Tmscfσstep)) ||
    (apply (rt_compatibility Tmcfσstep Tmscfσstep)) ||
    (apply (rt_compatibility Tmcfσstep Tmcfσstep)) ||
    (apply (rt_compatibility Tmscfσstep Tmcfσstep)).
  all: auto with AKcf sets.
  + apply (rt_compatibility Tmscfσstep Tmscfσstep (fun δ => Tmscf_snoc δ x)); auto with AKcf sets.
  + apply (rt_compatibility Tmscfσstep Tmscfσstep (fun δ => Tmscf_comp δ σ)); auto with AKcf sets.
  + apply (rt_compatibility Tmcfσstep Tmcfσstep (fun x => Tmcf_subst x δ)); auto with AKcf sets.
  + apply (rt_compatibility Tmcfσstep Tmcfσstep (fun x => Tmcf_app x y)); auto with AKcf sets.
Qed.

Lemma AKcfσconv_iter_π₁_compatibility (δ σ: Tmscf) (H: δ --s>* σ) (i: nat): cf_iter_π₁ i δ --s>* cf_iter_π₁ i σ.
Proof.
  apply (cf_iter_π₁_compatibility Tmcfσconv Tmscfσconv).
  - apply AKcfσconv_compatibility.
  - exact H.
Qed.

Lemma AKcfσconv_iter_π₂_compatibility (δ σ: Tmscf) (H: δ --s>* σ) (i: nat): cf_iter_π₂ i δ -->* cf_iter_π₂ i σ.
Proof.
  unfold cf_iter_π₂.
  apply (cf_π₂_step_compatibility Tmcfσconv Tmscfσconv).
  { apply AKcfσconv_compatibility. }
  apply AKcfσconv_iter_π₁_compatibility.
  exact H.
Qed.

Theorem AKcfσeq_compatibility : AKcf_compatible (Tmcfσeq) (Tmscfσeq).
Proof.
  apply make_AKcf_compatible; intros.
  all: try
    (apply (rst_compatibility Tmscfσstep Tmscfσstep)) ||
    (apply (rst_compatibility Tmcfσstep Tmscfσstep)) ||
    (apply (rst_compatibility Tmcfσstep Tmcfσstep)) ||
    (apply (rst_compatibility Tmscfσstep Tmcfσstep)).
  all: auto with AKcf sets.
  + apply (rst_compatibility Tmscfσstep Tmscfσstep (fun δ => Tmscf_snoc δ x)); auto with AKcf sets.
  + apply (rst_compatibility Tmscfσstep Tmscfσstep (fun δ => Tmscf_comp δ σ)); auto with AKcf sets.
  + apply (rst_compatibility Tmcfσstep Tmcfσstep (fun x => Tmcf_subst x δ)); auto with AKcf sets.
  + apply (rst_compatibility Tmcfσstep Tmcfσstep (fun x => Tmcf_app x y)); auto with AKcf sets.
Qed.

Lemma AKcfσeq_iter_π₁_compatibility (δ σ: Tmscf) (H: δ <--s>* σ) (i: nat): cf_iter_π₁ i δ <--s>* cf_iter_π₁ i σ.
Proof.
  apply (cf_iter_π₁_compatibility Tmcfσeq Tmscfσeq).
  - apply AKcfσeq_compatibility.
  - exact H.
Qed.

Lemma AKcfσeq_iter_π₂_compatibility (δ σ: Tmscf) (H: δ <--s>* σ) (i: nat): cf_iter_π₂ i δ <-->* cf_iter_π₂ i σ.
Proof.
  unfold cf_iter_π₂.
  apply (cf_π₂_step_compatibility Tmcfσeq Tmscfσeq).
  { apply AKcfσeq_compatibility. }
  apply AKcfσeq_iter_π₁_compatibility.
  exact H.
Qed.

Definition HINTsnoc_Tmscf_step_compatibility {δ' δ : Tmscf} {x : Tmcf} (H : δ' --s>* δ) : (Tmscf_snoc δ' x) --s>* (Tmscf_snoc δ x) := snoc_Tmscf_step_compatibility Tmcfσconv Tmscfσconv AKcfσconv_compatibility (x:=x) H.
Definition HINTsnoc_Tmcf_step_compatibility {x' x : Tmcf} {δ : Tmscf} (H : x' -->* x ) : (Tmscf_snoc δ x') --s>* (Tmscf_snoc δ x) := snoc_Tmcf_step_compatibility Tmcfσconv Tmscfσconv AKcfσconv_compatibility (δ:=δ) H.
Definition HINTcf_compl_step_compatibility {δ' δ : Tmscf} {σ : Tmscf} (H : δ' --s>* δ) : (Tmscf_comp δ' σ) --s>* (Tmscf_comp δ σ) := cf_compl_step_compatibility Tmcfσconv Tmscfσconv AKcfσconv_compatibility (σ:=σ) H .
Definition HINTcf_compr_step_compatibility {σ' σ : Tmscf} {δ : Tmscf} (H : σ' --s>* σ) : (Tmscf_comp δ σ') --s>* (Tmscf_comp δ σ) := cf_compr_step_compatibility Tmcfσconv Tmscfσconv AKcfσconv_compatibility (δ:=δ) H.
Definition HINTcf_π₁_step_compatibility {δ' δ : Tmscf} (H : δ' --s>* δ) : (Tmscf_π₁ δ') --s>* (Tmscf_π₁ δ) := cf_π₁_step_compatibility Tmcfσconv Tmscfσconv AKcfσconv_compatibility H.
Definition HINTsubst_Tmcf_step_compatibility {x' x : Tmcf} {δ : Tmscf} (H : x' -->* x ) : (Tmcf_subst x' δ) -->* (Tmcf_subst x δ) := subst_Tmcf_step_compatibility Tmcfσconv Tmscfσconv AKcfσconv_compatibility (δ:=δ) H.
Definition HINTsubst_Tmscf_step_compatibility {δ' δ : Tmscf} {x : Tmcf} (H : δ' --s>* δ) : (Tmcf_subst x δ') -->* (Tmcf_subst x δ) := subst_Tmscf_step_compatibility Tmcfσconv Tmscfσconv AKcfσconv_compatibility (x:=x) H.
Definition HINTcf_π₂_step_compatibility {δ' δ : Tmscf} (H : δ' --s>* δ) : (Tmcf_π₂ δ') -->* (Tmcf_π₂ δ) := cf_π₂_step_compatibility Tmcfσconv Tmscfσconv AKcfσconv_compatibility H.
Definition HINTcf_rator_step_compatibility {x' x y : Tmcf} (H : x' -->* x ) : (Tmcf_app x' y) -->* (Tmcf_app x y) := cf_rator_step_compatibility Tmcfσconv Tmscfσconv AKcfσconv_compatibility H.
Definition HINTcf_rand_step_compatibility {x y' y : Tmcf} (H : y' -->* y ) : (Tmcf_app x y') -->* (Tmcf_app x y) := cf_rand_step_compatibility Tmcfσconv Tmscfσconv AKcfσconv_compatibility H.
Definition HINTcf_lam_step_compatibility {x' x : Tmcf} (H : x' -->* x ) : (Tmcf_lam x') -->* (Tmcf_lam x) := cf_lam_step_compatibility Tmcfσconv Tmscfσconv AKcfσconv_compatibility H.

#[export] Hint Resolve HINTsnoc_Tmscf_step_compatibility  : AKcf.
#[export] Hint Resolve HINTsnoc_Tmcf_step_compatibility : AKcf.
#[export] Hint Resolve HINTcf_compl_step_compatibility : AKcf.
#[export] Hint Resolve HINTcf_compr_step_compatibility : AKcf.
#[export] Hint Resolve HINTcf_π₁_step_compatibility : AKcf.
#[export] Hint Resolve HINTsubst_Tmcf_step_compatibility : AKcf.
#[export] Hint Resolve HINTsubst_Tmscf_step_compatibility : AKcf.
#[export] Hint Resolve HINTcf_π₂_step_compatibility : AKcf.
#[export] Hint Resolve HINTcf_rator_step_compatibility : AKcf.
#[export] Hint Resolve HINTcf_rand_step_compatibility : AKcf.
#[export] Hint Resolve HINTcf_lam_step_compatibility : AKcf.

Ltac autored := fold Tmscfσconv; fold Tmcfσconv; auto with AKcf sets.