Set Warnings "-notation-overridden, -parsing".
From mathcomp Require Import boot.
Set Warnings "notation-overridden, parsing".
From Stdlib Require Import Relations Classes.RelationClasses.
#[warnings="-notation-overridden"]
From CwFdeBruijn.Syntax Require Import
  AKcf.AKcf_Conv
  Semantics.Monoid
  Semantics.Module
  Semantics.Kmm
  AKcf.substid
  Quotients.AKcfQuot
  AKcf.nf_uniqueness.

Local Open Scope quotient_scope.

Definition TmscfM_mnd_op' := lift_op2 TmscfσQ Tmscf_comp.

Lemma TmscfM_mnd_op'_lift : {morph \pi : x y / Tmscf_comp x y >-> (TmscfM_mnd_op' x y)}.
Proof.
  unlock TmscfM_mnd_op' => δ σ /=.
  apply/eqquotP.
  apply (introT (Tmscfσconv_spec _ _)).
  rewrite !unlock.
  eapply clos_rt_clos_rst.
  apply (cf_comp_parallelcompatibility Tmcfσconv Tmscfσconv).
  - apply clos_rt_is_preorder.
  - apply AKcfσconv_compatibility.
  - apply nffun_conv.
  - apply nffun_conv.
Defined.

Canonical TmscfM_mnd_op'_lift' := PiMorph2 TmscfM_mnd_op'_lift.
(*Now this will be rewritten automatically with piE*)

Definition TmscfM_mnd_op : TmscfσQ * TmscfσQ -> TmscfσQ
  := fun '(δ,σ) => TmscfM_mnd_op' δ σ.

Program Definition TmscfM : Monoid := {|
  mnd_obj :=  TmscfσQ;
  mnd_unit _ := \pi Tmscf_id;
  mnd_op := TmscfM_mnd_op
|}.

Next Obligation.
  apply extensionality.
  intros [[δ σ] τ].
  rewrite /compose /=.
  rewrite -(reprK σ) -(reprK τ) -(reprK δ) !piE.
  apply /eqquotP /Tmscfσconv_spec.
  apply rst_sym.
  autored.
Defined.
Next Obligation.
  apply extensionality.
  intros [tt δ].
  rewrite /compose /=.
  rewrite -(reprK δ) !piE.
  apply /eqquotP /Tmscfσconv_spec.
  autored.
Defined.
Next Obligation.
  apply extensionality.
  intros [δ tt].
  rewrite /compose /=.
  rewrite -(reprK δ) !piE.
  apply /eqquotP /Tmscfσconv_spec.
  autored.
Defined.

Definition TmcfM_mod_act' := lift_op21 TmcfσQ TmscfσQ TmcfσQ Tmcf_subst.

Lemma TmcfM_mod_act'_lift :
forall (x : Tmcf) (y : Tmscf), \pi_TmcfσQ (Tmcf_subst x y) = TmcfM_mod_act' (\pi_TmcfσQ x) (\pi_TmscfσQ y).
Proof.
  unlock TmcfM_mod_act' => x δ /=.
  apply/eqquotP.
  apply (introT (Tmcfσconv_spec _ _)).
  rewrite !unlock.
  eapply clos_rt_clos_rst.
  apply (cf_subst_parallelcompatibility Tmcfσconv Tmscfσconv).
  - apply clos_rt_is_preorder.
  - apply clos_rt_is_preorder.
  - apply AKcfσconv_compatibility.
  - apply nffun_conv.
  - apply nffun_conv.
Defined.

Canonical TmcfM_mod_act'_lift' := PiMorph21 TmcfM_mod_act'_lift.

Definition TmcfM_mod_act : TmcfσQ * TmscfσQ -> TmcfσQ
  := fun '(x,δ) => TmcfM_mod_act' x δ.

Program Definition TmcfM : Mod TmscfM := {|
  mod_obj := TmcfσQ;
  mod_action := TmcfM_mod_act
|}.

Next Obligation.
  apply extensionality.
  intros [[x δ] σ].
  rewrite /compose /=.
  rewrite -(reprK x) -(reprK δ) -(reprK σ) !piE.
  apply /eqquotP /Tmcfσconv_spec.
  autored.
Defined.
Next Obligation.
  apply extensionality.
  intros [x tt].
  rewrite /compose /=.
  rewrite -(reprK x) !piE.
  apply /eqquotP /Tmcfσconv_spec.
  apply subst_id.
Defined.

Definition AKcfM_snoc' := lift_op21 TmscfσQ TmcfσQ TmscfσQ Tmscf_snoc.
Lemma AKcfM_snoc'_lift : forall (δ : Tmscf) (x : Tmcf),
  \pi_TmscfσQ (Tmscf_snoc δ x) = AKcfM_snoc' (\pi_TmscfσQ δ) (\pi_TmcfσQ x).
Proof.
  unlock AKcfM_snoc' => x δ /=.
  apply/eqquotP.
  apply (introT (Tmscfσconv_spec _ _)).
  rewrite !unlock.
  eapply clos_rt_clos_rst.
  apply (cf_snoc_parallelcompatibility Tmcfσconv Tmscfσconv).
  - apply clos_rt_is_preorder.
  - apply clos_rt_is_preorder.
  - apply AKcfσconv_compatibility.
  - apply nffun_conv.
  - apply nffun_conv.
Qed.
Canonical AKcfM_snoc'_lift' := PiMorph21 AKcfM_snoc'_lift.

Definition AKcfM_snoc : TmscfM * TmcfM -> TmscfM
  := fun '(δ,x) => AKcfM_snoc' δ x.

Program Definition snocModMor : ModMorphism (ProdMod (MonoidMod TmscfM) TmcfM) (MonoidMod TmscfM) := {|
  modmor :=  AKcfM_snoc;
|}.
Next Obligation.
apply extensionality.
intros [[δ σ] τ].
rewrite /compose/bimap/AKcfM_snoc/=.
rewrite -(reprK δ) -(reprK σ) -(reprK τ) !piE.
apply/eqquotP.
apply (introT (Tmscfσconv_spec _ _)).
autored.
Qed.

Definition AKcfM_app' := lift_op21 TmcfσQ TmcfσQ TmcfσQ Tmcf_app.
Lemma AKcfM_app'_lift : forall (x : Tmcf) (y : Tmcf),
  \pi_TmcfσQ (Tmcf_app x y) = AKcfM_app' (\pi_TmcfσQ x) (\pi_TmcfσQ y).
Proof.
  unlock AKcfM_app' => x y /=.
  apply/eqquotP.
  apply (introT (Tmcfσconv_spec _ _)).
  rewrite !unlock.
  eapply clos_rt_clos_rst.
  apply (cf_app_parallelcompatibility Tmcfσconv Tmscfσconv).
  - apply clos_rt_is_preorder.
  - apply AKcfσconv_compatibility.
  - apply nffun_conv.
  - apply nffun_conv.
Qed.
Canonical AKcfM_app'_lift' := PiMorph21 AKcfM_app'_lift.

Definition AKcfM_app : TmcfM * TmcfM -> TmcfM
  := fun '(x,y) => AKcfM_app' x y.

Program Definition appModMor : ModMorphism (ProdMod TmcfM TmcfM) TmcfM := {|
  modmor :=  AKcfM_app;
|}.
Next Obligation.
apply extensionality.
intros [[x y] z].
rewrite /compose/bimap/AKcfM_app/=.
rewrite -(reprK x) -(reprK y) -(reprK z) !piE.
apply/eqquotP.
apply (introT (Tmcfσconv_spec _ _)).
autored.
Qed.

Definition AKcfM_π1' := lift_op1 TmscfσQ Tmscf_π₁.
Lemma AKcfM_π1'_lift : {morph \pi : x / Tmscf_π₁ x >-> AKcfM_π1' x}.
Proof.
  unlock AKcfM_π1' => δ /=.
  apply/eqquotP.
  apply (introT (Tmscfσconv_spec _ _)).
  rewrite !unlock.
  eapply clos_rt_clos_rst.
  apply HINTcf_π₁_step_compatibility.
  apply nffun_conv.
Qed.
Canonical AKcfM_π1'_lift' := PiMorph1 AKcfM_π1'_lift.

Definition AKcfM_π2' := lift_op11 TmscfσQ TmcfσQ Tmcf_π₂.
(* Lemma AKcfM_π2'_lift : {morph \pi : δ / Tmcf_π₂ δ >-> AKcfM_π2' δ}. *)
Lemma AKcfM_π2'_lift : forall (δ : Tmscf),
  \pi_TmcfσQ (Tmcf_π₂ δ) = AKcfM_π2' (\pi_TmscfσQ δ).
Proof.
  unlock AKcfM_π2' => δ /=.
  apply/eqquotP.
  apply (introT (Tmcfσconv_spec _ _)).
  rewrite !unlock.
  eapply clos_rt_clos_rst.
  apply HINTcf_π₂_step_compatibility.
  apply nffun_conv.
Qed.
Canonical AKcfM_π2'_lift' := PiMorph11 AKcfM_π2'_lift.

Definition πM (δ : TmscfM) : TmscfM * TmcfM := (AKcfM_π1' δ,  AKcfM_π2' δ).

Program Definition πModMor
  : ModMorphism (MonoidMod TmscfM) (ProdMod (MonoidMod TmscfM) TmcfM) := {|
  modmor :=  πM;
|}.
Next Obligation.
  apply extensionality.
  intros [δ σ].
  rewrite /compose/bimap/πM/mod_action/=/compose/bimap/=.
  apply pair_equal_spec.
  rewrite -(reprK δ) -(reprK σ) !piE.
  split.
  + apply/eqquotP.
    apply (introT (Tmscfσconv_spec _ _)).
    autored.
  + apply/eqquotP.
    apply (introT (Tmcfσconv_spec _ _)).
    autored.
Qed.
Program Definition πModIso
  : ModIsomorphism (MonoidMod TmscfM) (ProdMod (MonoidMod TmscfM) TmcfM) := {|
    modiso := πModMor;
    modiso_is := {|
      inv := snocModMor
    |}
  |}.
Next Obligation.
  apply extensionality.
  intros [δ x].
  rewrite /compose/=.
  apply pair_equal_spec.
  rewrite -(reprK δ) -(reprK x) !piE.
  split.
  + apply/eqquotP.
  apply (introT (Tmscfσconv_spec _ _)).
  autored.
  + apply/eqquotP.
  apply (introT (Tmcfσconv_spec _ _)).
  autored.
Qed.
Next Obligation.
  apply extensionality.
  intros δ.
  rewrite /compose/Datatypes.id/=.
  rewrite -(reprK δ) !piE.
  apply/eqquotP.
  apply (introT (Tmscfσconv_spec _ _)).
  autored.
Qed.

Definition AKcfM_lam := lift_op1 TmcfσQ Tmcf_lam.
Lemma AKcfM_lam_lift : {morph \pi : x / Tmcf_lam x >-> AKcfM_lam x}.
Proof.
  unlock AKcfM_lam => t /=.
  apply/eqquotP.
  apply (introT (Tmcfσconv_spec _ _)).
  rewrite !unlock.
  eapply clos_rt_clos_rst.
  apply HINTcf_lam_step_compatibility.
  apply nffun_conv.
Qed.
Canonical AKcfM_lam_lift' := PiMorph1 AKcfM_lam_lift.

Definition AKcfM_deriv := lift_op1 TmscfσQ lift.
Lemma AKcfM_deriv_lift : {morph \pi : x / lift x >-> AKcfM_deriv x}.
Proof.
  unlock AKcfM_deriv => t /=.
  apply/eqquotP.
  apply (introT (Tmscfσconv_spec _ _)).
  rewrite !unlock.
  eapply clos_rt_clos_rst.
  apply lift_compatibility.
  apply nffun_conv.
Qed.
Canonical AKcfM_deriv_lift' := PiMorph1 AKcfM_deriv_lift.

Definition AKcf_kmm : KMM := {|
  kmm_mnd := TmscfM;
  kmm_mod := TmcfM;
  kiso := πModIso
|}.

Program Definition lamModMor : ModMorphism (DerivMod AKcf_kmm) AKcf_kmm := {|
  modmor :=  AKcfM_lam;
|}.
Next Obligation.
apply extensionality.
intros [x y].
rewrite /compose/bimap/=.
rewrite -(reprK x) -(reprK y) !piE.
apply/eqquotP.
apply (introT (Tmcfσconv_spec _ _)).
autored.
Qed.

Definition AKcf : KMMλappmodel := {|
  KMMλappmodel_kmm := AKcf_kmm;
  kmm_app := appModMor;
  kmm_lam := lamModMor
|}.