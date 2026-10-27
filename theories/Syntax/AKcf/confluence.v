
From CwFdeBruijn.Syntax.AKcf Require Export normalization substid.

Lemma confluencingσcompatible : AKcf_compatible (confluencing Tmcfσstep) (confluencing Tmscfσstep).
Proof.
  apply make_AKcf_compatible; intros.
  - destruct H as [σ [? ?]].
    exists (Tmscf_snoc σ x); autored.
  - destruct H as [y [? ?]].
    exists (Tmscf_snoc δ y); autored.
  - destruct H as [τ [? ?]].
    exists (Tmscf_comp τ σ); autored.
  - destruct H as [τ [? ?]].
    exists (Tmscf_comp δ τ); autored.
  - destruct H as [σ [? ?]].
    exists (Tmscf_π₁ σ); autored.
  - destruct H as [y [? ?]].
    exists (Tmcf_subst y δ); autored.
  - destruct H as [σ [? ?]].
    exists (Tmcf_subst x σ); autored.
  - destruct H as [σ [? ?]].
    exists (Tmcf_π₂ σ); autored.
  - destruct H as [t [? ?]].
    exists (Tmcf_app t y); autored.
  - destruct H as [t [? ?]].
    exists (Tmcf_app x t); autored.
  - destruct H as [y [? ?]].
    exists (Tmcf_lam y); autored.
Qed.

Section confluenceCases.

  Local Lemma confluencing_parallelapp_compatible {x x' y y'}
    (conf_x : confluencing Tmcfσstep x x')
    (conf_y : confluencing Tmcfσstep y y')
    : confluencing Tmcfσstep (Tmcf_app x y) (Tmcf_app x' y').
  Proof.
    destruct conf_x as [x'' [? ?]].
    destruct conf_y as [y'' [? ?]].
    exists (Tmcf_app x'' y'').
    split;
    eapply (cf_app_parallelcompatibility _ (clos_refl_trans _ Tmscfσstep) _ AKcfσconv_compatibility); assumption. Unshelve.
    all : apply clos_rt_is_preorder.
  Qed.

  Local Lemma confluencing_compsnocid {δ t}
  : confluencing Tmscfσstep
    (Tmscf_snoc δ t)
    (Tmscf_snoc (Tmscf_comp δ Tmscf_id) (Tmcf_subst t Tmscf_id)).
  Proof.
    destruct (Tmcf_normalization t) as [t0  [tred nf_t] ].
    exists (Tmscf_snoc δ t0); split.
    - apply HINTsnoc_Tmcf_step_compatibility.
      auto with AKcf sets.
    - eapply rt_trans.
      + eapply HINTsnoc_Tmscf_step_compatibility.
        onestep. apply cf_idr.
      + eapply HINTsnoc_Tmcf_step_compatibility.
        eapply rt_trans.
        { eapply HINTsubst_Tmcf_step_compatibility.
          exact tred. }
        apply V_subst_id.
        apply (Tmcfσnf_is_value nf_t).
  Qed.

  Local Lemma confluencing_substsubstlam {t δ σ}
  : confluencing Tmcfσstep
    (Tmcf_subst (Tmcf_lam t) (Tmscf_comp δ σ))
    (Tmcf_subst (Tmcf_lam (Tmcf_subst t (lift δ))) σ).
  Proof.
    split with (Tmcf_lam (Tmcf_subst t (Tmscf_snoc
                    (Tmscf_comp δ (Tmscf_comp σ (Tmscf_π₁ Tmscf_id)))
                    (Tmcf_π₂ Tmscf_id))));
    split.
    - eapply rt_trans. { onestep. apply cf_lamsubst. }
    apply HINTcf_lam_step_compatibility.
    apply HINTsubst_Tmscf_step_compatibility.
    apply HINTsnoc_Tmscf_step_compatibility.
    onestep. apply cf_ass.
    - eapply rt_trans. { onestep. apply cf_lamsubst. }
    apply HINTcf_lam_step_compatibility.
    eapply rt_trans. { onestep. apply cf_substsubst. }
    apply HINTsubst_Tmscf_step_compatibility.
    eapply rt_trans. { onestep. apply cf_snocomp. }
    eapply rt_trans.
    {
      eapply HINTsnoc_Tmcf_step_compatibility.
      eapply rt_trans. { onestep. apply cf_substπ₂. }
      eapply rt_trans.
      { eapply HINTcf_π₂_step_compatibility.
        onestep. apply cf_idl. }
      onestep. apply cf_π₂beta.
    }
    apply HINTsnoc_Tmscf_step_compatibility.
    eapply rt_trans. { onestep. apply cf_ass. }
    apply HINTcf_compr_step_compatibility.
    eapply rt_trans.
    { eapply rt_trans. {onestep. apply cf_π₁comp. }
      eapply HINTcf_π₁_step_compatibility.
      onestep. apply cf_idl. }
    onestep. apply cf_π₁beta.
  Qed.

  Local Lemma confluencing_substsubstπ₂ {σ δ τ}
  : confluencing Tmcfσstep
      (Tmcf_subst (Tmcf_π₂ σ) (Tmscf_comp δ τ))
      (Tmcf_subst (Tmcf_π₂ (Tmscf_comp σ δ)) τ).
  Proof.
    split with (Tmcf_π₂ (Tmscf_comp σ (Tmscf_comp δ τ)));
      split; auto with AKcf sets.
    eapply rt_trans. { onestep. apply cf_substπ₂. }
    auto with AKcf sets.
  Qed.

  Local Lemma confluencing_substsubstsubst {t δ σ τ}
  : confluencing Tmcfσstep
    (Tmcf_subst (Tmcf_subst t δ) (Tmscf_comp σ τ))
    (Tmcf_subst (Tmcf_subst t (Tmscf_comp δ σ)) τ).
  Proof.
    split with (Tmcf_subst t (Tmscf_comp δ (Tmscf_comp σ τ)));
      split; auto with AKcf sets.
    eapply rt_trans. { onestep. apply cf_substsubst. }
    auto with AKcf sets.
  Qed.

  Local Lemma confluencing_substsubstapp {x y δ σ}
  : confluencing Tmcfσstep
    (Tmcf_subst (Tmcf_app x y) (Tmscf_comp δ σ))
    (Tmcf_subst (Tmcf_app (Tmcf_subst x δ) (Tmcf_subst y δ)) σ).
  Proof.
    exists (Tmcf_app
      (Tmcf_subst x (Tmscf_comp δ σ))
      (Tmcf_subst y (Tmscf_comp δ σ))); split.
    - autored.
    - eapply rt_trans. { onestep. apply cf_appsubst. }
      eapply rt_trans.
      { eapply HINTcf_rator_step_compatibility.
        onestep. apply cf_substsubst. }
      eapply HINTcf_rand_step_compatibility.
      onestep. apply cf_substsubst.
  Qed.

  Local Lemma confluencing_substsubst_compatibility {x x' δ δ' σ σ'}
  (step_x: x' -->* x)
  (step_δ: δ' --s>* δ)
  (step_σ: σ' --s>* σ)
  : confluencing Tmcfσstep
    (Tmcf_subst (Tmcf_subst x δ) σ)
    (Tmcf_subst x' (Tmscf_comp δ' σ')).
  Proof.
    exists (Tmcf_subst x (Tmscf_comp δ σ)); split.
    - auto with AKcf sets.
    - eapply rt_trans.
      { eapply HINTsubst_Tmcf_step_compatibility.
        exact step_x. }
      apply HINTsubst_Tmscf_step_compatibility.
      eapply rt_trans.
      + eapply HINTcf_compl_step_compatibility.
        apply step_δ.
      + eapply HINTcf_compr_step_compatibility.
        apply step_σ.
  Qed.

  Local Lemma confluencing_substlam_compatibility {x x' δ δ'}
  (step_x: x' -->* x)
  (step_δ: δ' --s>* δ)
  : confluencing Tmcfσstep
    (Tmcf_subst (Tmcf_lam x) δ)
    (Tmcf_lam (Tmcf_subst x' (lift δ'))).
  Proof.
    exists (Tmcf_lam (Tmcf_subst x (lift δ))); split.
    - auto with AKcf sets.
    - apply HINTcf_lam_step_compatibility.
      eapply rt_trans.
      { eapply HINTsubst_Tmcf_step_compatibility.
        exact step_x. }
      apply HINTsubst_Tmscf_step_compatibility.
      apply lift_compatibility.
      apply step_δ.
  Qed.

  Local Lemma confluencing_substπ₂_compatibility {δ δ' σ σ'}
  (step_δ: δ' --s>* δ)
  (step_σ: σ' --s>* σ)
  : confluencing Tmcfσstep
    (Tmcf_subst (Tmcf_π₂ δ) σ)
    (Tmcf_π₂ (Tmscf_comp δ' σ')).
  Proof.
    exists (Tmcf_π₂ (Tmscf_comp δ σ)); split; auto with AKcf sets.
    eapply rt_trans with (Tmcf_π₂ (Tmscf_comp δ' σ)); fold Tmcfσconv; auto 7 with AKcf sets.
  Qed.

  Local Lemma confluencing_substapp_compatibility {x x' y y' δ δ'}
  (red_x: x' -->* x)
  (red_y: y' -->* y)
  (red_δ: δ' --s>* δ)
  : confluencing Tmcfσstep
    (Tmcf_subst (Tmcf_app x y) δ)
    (Tmcf_app (Tmcf_subst x' δ') (Tmcf_subst y' δ')).
  Proof.
    exists (Tmcf_app (Tmcf_subst x δ) (Tmcf_subst y δ)); split; autored.
    eapply rt_trans.
    { eapply HINTcf_rator_step_compatibility.
      eapply rt_trans.
      { eapply HINTsubst_Tmcf_step_compatibility.
        exact red_x. }
      eapply HINTsubst_Tmscf_step_compatibility.
      exact red_δ. }
    apply HINTcf_rand_step_compatibility.
    eapply rt_trans.
    { eapply HINTsubst_Tmcf_step_compatibility.
      exact red_y. }
    eapply HINTsubst_Tmscf_step_compatibility.
    exact red_δ.
  Qed.

  Local Lemma confluencing_π₂snoc_compatibility {x x' δ}
  (red_x: x' -->* x)
  : confluencing Tmcfσstep x' (Tmcf_π₂ (Tmscf_snoc δ x)).
  Proof.
    exists x; split; auto with AKcf sets.
  Qed.

  Local Lemma confluencing_subst {x y z δ}
  (Hy : Tmcfσstep' (Tmcf_subst x δ) y)
  (Hz : x --> z)
  : confluencing Tmcfσstep y (Tmcf_subst z δ).
  Proof.
    inversion Hy; subst.
    - inversion Hz; subst.
      + inversion H; subst.
        * apply confluencing_substsubstsubst.
        * apply confluencing_substsubstlam.
        * apply confluencing_substsubstπ₂.
        * apply (confluencing_substsubstapp).
      + apply confluencing_comm.
        apply confluencing_substsubst_compatibility;
          auto with AKcf sets.
      + apply confluencing_comm.
        apply confluencing_substsubst_compatibility;
          auto with AKcf sets.
    - inversion Hz; subst; try solve_by_invert.
      apply confluencing_comm.
      apply confluencing_substlam_compatibility;
        auto with AKcf sets.
    - inversion Hz; subst.
      + inversion H; subst.
        apply confluencing_red.
        eapply rt_trans.
        { eapply HINTcf_π₂_step_compatibility.
          onestep. apply cf_snocomp. }
        onestep. apply cf_π₂beta.
      + apply confluencing_comm.
        apply confluencing_substπ₂_compatibility;
          auto with AKcf sets.
    - inversion Hz; subst; try solve_by_invert.
      + apply confluencing_comm.
        apply confluencing_substapp_compatibility;
        autored.
      + apply confluencing_comm.
        apply confluencing_substapp_compatibility;
        autored.
  Qed.

  Local Lemma confluencing_subst' {x y δ δ'}
  (H : Tmcfσstep' (Tmcf_subst x δ') y)
  (H0 : δ' --s> δ)
  : confluencing Tmcfσstep y (Tmcf_subst x δ).
  Proof.
    inversion H; subst.
      + apply confluencing_comm.
        apply confluencing_substsubst_compatibility; autored.
      + apply confluencing_comm.
        apply confluencing_substlam_compatibility; autored.
      + apply confluencing_comm.
        apply confluencing_substπ₂_compatibility; autored.
      + apply confluencing_comm.
        apply confluencing_substapp_compatibility; autored.
  Qed.

  Local Lemma confluencing_π₂ {x δ' δ}
  (H: Tmcfσstep' (Tmcf_π₂ δ') x)
  (red_δ : δ' --s> δ)
  : confluencing Tmcfσstep x (Tmcf_π₂ δ).
  Proof.
    inversion H; subst.
    inversion red_δ; subst.
    - inversion H0; subst.
      apply confluencing_refl.
    - apply confluencing_π₂snoc_compatibility.
      auto with AKcf sets.
    - apply (confluencing_π₂snoc_compatibility);
        apply rt_step; exact H3.
  Qed.

  Local Lemma confluencing_compcomp {δ σ ν τ}
  (H : (Tmscf_comp δ σ) --s> τ)
  : confluencing Tmscfσstep (Tmscf_comp δ (Tmscf_comp σ ν)) (Tmscf_comp τ ν).
  Proof.
    inversion H; subst.
    - inversion H0; subst.
      + exists (Tmscf_comp τ ν).
        auto 6 with AKcf sets.
      + exists (Tmscf_comp τ ν).
        auto 6 with AKcf sets.
      + exists (Tmscf_comp σ0 (Tmscf_comp δ0 (Tmscf_comp σ ν))); split.
        **autored.
        **eapply rt_trans. { onestep. apply cf_ass. }
          apply HINTcf_compr_step_compatibility.
          autored.
      + exists (Tmscf_snoc (Tmscf_comp δ0 (Tmscf_comp σ ν)) (Tmcf_subst t (Tmscf_comp σ ν))); split.
        **auto with AKcf sets.
        **eapply rt_trans.
          { onestep. apply cf_snocomp. }
          eapply rt_trans.
          { eapply HINTsnoc_Tmscf_step_compatibility.
            onestep. apply cf_ass. }
          apply HINTsnoc_Tmcf_step_compatibility.
          autored.
      + exists (Tmscf_π₁ (Tmscf_comp δ0 (Tmscf_comp σ ν)));
        split; autored.
        eapply rt_trans with (Tmscf_π₁ (Tmscf_comp (Tmscf_comp δ0 σ) ν)); auto with AKcf sets.
    - exists (Tmscf_comp δ0 (Tmscf_comp σ ν)).
      auto with AKcf sets.
    - exists (Tmscf_comp δ (Tmscf_comp σ0 ν)).
      auto 6 with AKcf sets.
  Qed.

  Local Lemma confluencing_compsnoc {δ σ t δt}
  (H : (Tmscf_snoc δ t) --s> δt)
  : confluencing Tmscfσstep
    (Tmscf_snoc (Tmscf_comp δ σ) (Tmcf_subst t σ))
    (Tmscf_comp δt σ).
  Proof.
    inversion H; subst.
    - inversion H0; subst.
      apply confluencing_red.
      eapply rt_trans.
      { eapply HINTsnoc_Tmscf_step_compatibility.
        onestep.
        apply cf_π₁comp. }
      eapply rt_trans.
      { eapply HINTsnoc_Tmcf_step_compatibility.
        onestep.
        apply cf_substπ₂. }
      auto with AKcf sets.
    - exists (Tmscf_snoc (Tmscf_comp δ0 σ) (Tmcf_subst t σ)).
      auto 6 with AKcf sets.
    - split with (Tmscf_snoc (Tmscf_comp δ σ) (Tmcf_subst x σ)).
      auto 6 with AKcf sets.
  Qed.

  Local Lemma confluenicing_compπ₁ {δ δ₁ σ}
  (H : (Tmscf_π₁ δ) --s> δ₁)
  : confluencing Tmscfσstep
    (Tmscf_π₁ (Tmscf_comp δ σ))
    (Tmscf_comp δ₁ σ).
  Proof.
    inversion H; subst.
    - inversion H0; subst.
      apply confluencing_red.
      eapply rt_trans.
      { eapply HINTcf_π₁_step_compatibility.
        onestep. apply cf_snocomp. }
      autored.
    - exists (Tmscf_π₁ (Tmscf_comp δ0 σ)); split; autored.
  Qed.

  Local Lemma confluencing_comp {δ δ' σ δσ}
  (H : Tmscfσstep' (Tmscf_comp δ' σ) δσ)
  (red_δ : δ' --s> δ)
  : confluencing Tmscfσstep δσ (Tmscf_comp δ σ).
  Proof.
    inversion H; subst; try solve_by_inverts 2.
    - exists δ; split; autored.
    - eapply (confluencing_compcomp red_δ).
    - apply (confluencing_compsnoc red_δ).
    - apply (confluenicing_compπ₁ red_δ).
  Qed.

  Local Lemma confluencing_comp' {δ σ σ' δσ}
  (H : Tmscfσstep' (Tmscf_comp δ σ') δσ)
  (red_σ : σ' --s> σ)
  : confluencing Tmscfσstep (Tmscf_comp δ σ) δσ.
  Proof.
    inversion H; subst.
    - split with σ.
      auto with AKcf sets.
    - try solve_by_inverts 2.
    - split with (Tmscf_comp σ0 (Tmscf_comp δ0 σ)).
      auto 6 with AKcf sets.
    - split with (Tmscf_snoc (Tmscf_comp δ0 σ) (Tmcf_subst t σ)).
      split; auto with AKcf sets.
      eapply rt_trans with (Tmscf_snoc (Tmscf_comp δ0 σ) (Tmcf_subst t σ')); auto with AKcf sets.
    - split with (Tmscf_π₁ (Tmscf_comp δ0 σ)).
      auto 6 with AKcf sets.
  Qed.

  Local Lemma confluencing_snoc {δ δ' x δx}
  (H : Tmscfσstep' (Tmscf_snoc δ' x) δx)
  (red_δ : δ' --s> δ)
  : confluencing Tmscfσstep δx (Tmscf_snoc δ x).
  Proof.
    inversion H; subst.
    inversion red_δ; subst.
    - inversion H0; subst.
      apply confluencing_comm.
      apply confluencing_red.
      auto with AKcf sets.
    - split with δ0.
      split.
      + autored.
      + eapply rt_trans.
        2:{ onestep. apply cf_πeta. }
        autored.
  Qed.

  Local Lemma confluencing_snoc' {δ x' x δx}
  (H : Tmscfσstep' (Tmscf_snoc δ x') δx)
  (red_x : x' --> x)
  : confluencing Tmscfσstep δx (Tmscf_snoc δ x).
  Proof.
    inversion H; subst.
    inversion red_x; subst.
    - inversion H0; subst.
      apply confluencing_comm.
      apply confluencing_red.
      auto with AKcf sets.
    - split with δ; split.
      + autored.
      + eapply rt_trans.
        2:{ onestep. apply cf_πeta. }
        autored.
  Qed.

  Local Lemma confluencing_π₁snoc_compatibility {δ δ' x}
  (red_δ: δ' --s>* δ)
  : confluencing Tmscfσstep δ' (Tmscf_π₁ (Tmscf_snoc δ x)).
  Proof.
    exists δ; split; autored.
  Qed.

  Local Lemma confluencing_π₁ {δ' δ σ}
  (H : Tmscfσstep' (Tmscf_π₁ δ') σ)
  (red_δ: δ' --s> δ)
  : confluencing Tmscfσstep σ (Tmscf_π₁ δ).
  Proof.
    inversion H; subst.
    inversion red_δ; subst.
    - inversion H0; subst.
      apply confluencing_refl.
    - apply confluencing_π₁snoc_compatibility.
      apply rt_step. exact H3.
    - exists σ; split; autored.
  Qed.

End confluenceCases.

Lemma Tmscfσstep'confluenceAt (δ : Tmscf)
  : confluenceAt Tmscfσstep' Tmscfσstep δ
with Tmcfσstep'confluenceAt (x : Tmcf)
  : confluenceAt Tmcfσstep' Tmcfσstep x.
Proof.
{ intros δ1 δ2 red1 red2.
  inversion red1; subst; inversion red2; subst.
  - apply confluencing_refl.
  - apply confluencing_refl.
  - apply confluencing_refl.
  - apply confluencing_refl.
  - exists (Tmscf_comp σ δ); split; auto with AKcf sets.
  - apply confluencing_compsnocid.
  - exists (Tmscf_π₁ δ); auto 6 with AKcf sets.
  - exists (Tmscf_comp σ δ0); auto 6 with AKcf sets.
  - apply confluencing_refl.
  - apply confluencing_comm.
    apply confluencing_compsnocid.
  - apply confluencing_refl.
  - apply confluencing_refl.
  - exists (Tmscf_π₁ δ0); auto 6 with AKcf sets.
  - apply confluencing_refl.
  - apply confluencing_refl.
}
{ intros x1 x2 red1 red2.
  inversion red1; subst; inversion red2; subst.
  - esplit; auto with sets.
  - esplit; auto with sets.
  - esplit; auto with sets.
  - esplit; auto with sets.
  - esplit; auto with sets.
}
Qed.

Fixpoint TmscfσstepconfluenceAt (δ : Tmscf)
  : confluenceAt Tmscfσstep Tmscfσstep δ
with TmcfσstepconfluenceAt (x : Tmcf)
  : confluenceAt Tmcfσstep Tmcfσstep x.
Proof.
  { intros δ1 δ2 red1 red2.
    inversion red1;
      inversion red2;
      try solve_by_inverts 2.
    - apply (Tmscfσstep'confluenceAt δ _ _ H H2).
    - subst. apply (confluencing_snoc H H2).
    - subst. apply (confluencing_snoc' H H2).
    - subst. apply (confluencing_comp H H2).
    - subst. apply confluencing_comm.
      eapply (confluencing_comp' H H2).
    - subst. apply (confluencing_π₁ H H2).
    - apply confluencing_comm.
      subst. apply (confluencing_snoc H2 H).
    -
      destruct δ; try discriminate H0; subst.
      subst.
      inversion H0; subst.
      inversion H3; subst.

      apply confluencingσcompatible.
      apply (TmscfσstepconfluenceAt δ _ _ H H2).
    - subst. inversion H3. subst.
      exists (Tmscf_snoc δ0 x0); split; autored.
    - apply confluencing_comm.
      subst. apply (confluencing_snoc' H2 H).
    - subst.  inversion H3. subst.
      exists (Tmscf_snoc δ3 x); split; autored.
    -
      destruct δ; try discriminate H0; subst.
      subst.
      inversion H0; subst.
      inversion H3; subst.

      apply confluencingσcompatible.
      apply (TmcfσstepconfluenceAt x1 _ _ H H2).
    - subst. apply confluencing_comm.
      eapply (confluencing_comp H2 H).
    -
      destruct δ; try discriminate H0; subst.
      subst.
      inversion H0; subst.
      inversion H3; subst.

      apply confluencingσcompatible.
      apply (TmscfσstepconfluenceAt δ4 _ _ H H2).
    - subst; inversion H3; subst.
      exists (Tmscf_comp δ0 σ0); autored.
    - subst. eapply (confluencing_comp' H2 H).
    - subst. inversion H3. subst.
      exists (Tmscf_comp δ3 σ); autored.
    -
      destruct δ; try discriminate H0; subst.
      subst.
      inversion H0; subst.
      inversion H3; subst.

      apply confluencingσcompatible.
      apply (TmscfσstepconfluenceAt δ5 _ _ H H2).
    - subst. apply confluencing_comm.
      apply (confluencing_π₁ H2 H).
    -
      destruct δ; try discriminate H0; subst.
      subst.
      inversion H0; subst.
      inversion H3; subst.

      apply confluencingσcompatible.
      apply (TmscfσstepconfluenceAt δ _ _ H H2).
  }
  {
    intros x1 x2 red1 red2.
    inversion red1;
      inversion red2;
      try solve_by_inverts 2.
    - subst. apply (Tmcfσstep'confluenceAt x x1 x2 H H2).
    - subst. apply (confluencing_subst H H2).
    - subst. apply (confluencing_subst' H H2).
    - subst. apply (confluencing_π₂ H H2).
    - subst. apply confluencing_comm.
      apply (confluencing_subst H2 H).
    -
      destruct x; try discriminate H0; subst.
      subst.
      inversion H0; subst.
      inversion H3; subst.

      apply confluencingσcompatible.
      apply (TmcfσstepconfluenceAt x _ _ H H2).
    - subst. inversion H3. subst.
      exists (Tmcf_subst x0 δ0); autored.
    - subst. apply confluencing_comm.
      eapply (confluencing_subst' H2 H).
    - subst. inversion H3. subst.
      exists (Tmcf_subst x3 δ); autored.
    -
      destruct x; try discriminate H0; subst.
      subst.
      inversion H0; subst.
      inversion H3; subst.

      apply confluencingσcompatible.
      eapply (TmscfσstepconfluenceAt δ1 _ _ H H2).
    - subst. apply confluencing_comm.
      eapply (confluencing_π₂ H2 H).
    -
      destruct x; try discriminate H0; subst.
      inversion H0; subst.
      inversion H3; subst.

      apply confluencingσcompatible.
      apply (TmscfσstepconfluenceAt δ1 _ _ H H2).
    -
      destruct x; try discriminate H0; subst.
      inversion H0; subst.
      inversion H3; subst.

      apply confluencingσcompatible.
      apply (TmcfσstepconfluenceAt x4 _ _ H H2).
    - subst; inversion H3; subst.
      apply confluencing_parallelapp_compatible;
      [apply confluencing_comm | idtac];
      apply confluencing_red;
      autored.
    - subst; inversion H3; subst.
      apply confluencing_parallelapp_compatible;
      [idtac | apply confluencing_comm];
      apply confluencing_red;
      autored.
    - destruct x; try discriminate H0; subst. 
      inversion H0; subst.
      inversion H3; subst.

      apply confluencingσcompatible.
      apply (TmcfσstepconfluenceAt x5 _ _ H H2).
    - destruct x; try discriminate H0; subst. 
      inversion H0; subst.
      inversion H3; subst.

      apply confluencingσcompatible.
      apply (TmcfσstepconfluenceAt x _ _ H H2).
  }
Qed.
