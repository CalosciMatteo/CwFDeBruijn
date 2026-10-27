From CwFdeBruijn.Syntax.AKcf Require Export Conv_Lemmas values normalization.
From CwFdeBruijn.Syntax.AKcf Require Import occur_Compatibility.

Lemma Tmscf_OccurAtP_cf_iter_π₁ (i pos:nat)
  : Tmscf_OccurAtP (i + pos) pos (cf_iter_π₁ i Tmscf_id).
Proof.
  revert pos. induction i; intro pos.
  - constructor.
  - simpl.
    constructor.
    assert (E:(S (i+pos) = i + (S pos))). {lia. } rewrite E.
    apply IHi.
Qed.

Lemma nocc_0_π₁lift {j:nat} {δ: Tmscf}
: ~ (Tmscf_OccurAtP 0 j (Tmscf_π₁ (lift δ))).
Proof.
  unfold lift.
  intro abs.
  inversion abs; subst.
  inversion occ_δ; subst.
  inversion occ_iδ; subst.
  inversion occ_ikδ₂; subst.
  inversion occ_δ0.
Qed.

Section nocc_nsubst0.
  Local Lemma nocc_nsubst' {x :Tmcf} {i:nat} (σ : Tmscf)
    (notneeded : Tmcfσvalue x)
    (nocc_0x : ~ Tmcf_OccurP i x)
    : exists t,
      (Tmcf_subst x (iter_lift i σ) -->* t) /\
      (forall z, Tmcf_subst x (iter_lift i (Tmscf_snoc (Tmscf_π₁ σ) z)) -->* t).
  Proof.
    revert σ i nocc_0x.
    induction notneeded; intros σ i nocc_0x.
    - destruct (cf_iter_π₁idP_to_cf_iter_π₁id Hδ) as [j ?]; subst.
      destruct (lt_eq_lt_dec j i) as [[le_ji|eq_ji]|le_ij].
      + exists (Tmcf_ref j); split.
        * eapply rt_trans.
          { onestep. apply cf_substπ₂. }
          eapply rt_trans.
          { eapply HINTcf_π₂_step_compatibility.
            apply Tmscf_compiterπid. }
          apply (cf_iter_π₂_lift _ _ le_ji).
        * intro z.
          eapply rt_trans.
          { onestep. apply cf_substπ₂. }
          eapply rt_trans.
          { eapply HINTcf_π₂_step_compatibility.
            apply Tmscf_compiterπid. }
          apply (cf_iter_π₂_lift _ _ le_ji).
      + subst.
        exfalso.
        apply nocc_0x.
        induction i.
        * repeat constructor.
        * constructor.
          assert (E:(S i = S i + 0)). {lia. } rewrite E at 1.
          apply Tmscf_OccurAtP_cf_iter_π₁.
      + destruct i.
        { destruct j.
          { exfalso. inversion le_ij. }
          exists (cf_iter_π₂ ((S j)) σ); split.
          + eapply rt_trans.
            { onestep. apply cf_substπ₂. }
            apply HINTcf_π₂_step_compatibility.
            apply Tmscf_compiterπid.
          + intro z.
            eapply rt_trans.
            { onestep. apply cf_substπ₂. }
            apply HINTcf_π₂_step_compatibility.
            eapply rt_trans.
            { apply Tmscf_compiterπid. }
            rewrite cf_iter_π₁_flip.
            eapply rt_trans.
            { apply AKcfσconv_iter_π₁_compatibility.
              onestep. apply cf_π₁beta. }
            rewrite <-cf_iter_π₁_flip.
            apply rt_refl.
        }
        exists (cf_iter_π₂ (j-(S i)) (Tmscf_comp σ (cf_iter_π₁ (S i) Tmscf_id))); split.
        * eapply rt_trans.
          { onestep. apply cf_substπ₂. }
          apply HINTcf_π₂_step_compatibility.
          eapply rt_trans.
          { apply Tmscf_compiterπid. }
          apply cf_iter_π₁_more_lift. exact le_ij.
        * intro z.
          eapply rt_trans.
          { onestep. apply cf_substπ₂. }
          apply HINTcf_π₂_step_compatibility.
          eapply rt_trans.
          { apply Tmscf_compiterπid. }
          eapply rt_trans.
          { apply cf_iter_π₁_more_lift. exact le_ij. }
          eapply rt_trans.
          { eapply AKcfσconv_iter_π₁_compatibility.
            onestep. apply cf_snocomp. }
          assert (E: j - S i = S (Nat.pred (j - S i))). { lia. }
          rewrite E at 1.
          rewrite cf_iter_π₁_flip.
          eapply rt_trans.
          { eapply AKcfσconv_iter_π₁_compatibility.
            eapply rt_trans.
            { onestep. apply cf_π₁beta. }
            onestep. apply cf_π₁comp. }
          rewrite <-cf_iter_π₁_flip, <-E.
          apply rt_refl.
    - destruct (IHnotneeded1 σ i) as [tx [red1tx red2tx]].
      {
        intro abs.
        apply nocc_0x.
        apply Tmcf_OccurP_rator.
        exact abs.
      }
      destruct (IHnotneeded2 σ i) as [ty [red1ty red2ty]].
      {
        intro abs.
        apply nocc_0x.
        apply Tmcf_OccurP_rand.
        exact abs.
      }
      exists (Tmcf_app tx ty); split.
      * eapply rt_trans.
        { onestep. apply cf_appsubst. }
        eapply rt_trans.
        { eapply HINTcf_rator_step_compatibility.
          exact red1tx. }
        eapply HINTcf_rand_step_compatibility.
        exact red1ty.
      * intro z.
        eapply rt_trans.
        { onestep. apply cf_appsubst. }
        eapply rt_trans.
        { eapply HINTcf_rator_step_compatibility.
          apply red2tx. }
        eapply HINTcf_rand_step_compatibility.
        apply red2ty.
    - destruct (IHnotneeded σ (S i))
        as [xs [red1xs red2xs]].
      { intro abs.
        apply nocc_0x.
        constructor.
        exact abs. }
      exists (Tmcf_lam xs); split.
      + eapply rt_trans.
        { onestep. apply cf_lamsubst. }
        eapply HINTcf_lam_step_compatibility.
        exact red1xs.
      + intro z.
        eapply rt_trans.
        { onestep. apply cf_lamsubst. }
        eapply HINTcf_lam_step_compatibility.
        apply red2xs.
  Qed.

  Local Lemma nocc_nsubst_variant' {x :Tmcf} {i:nat} (σ : Tmscf)
    (notneeded : Tmcfσvalue x)
    (nocc_0x : ~ Tmcf_OccurP i x)
    : exists y, forall z,
      Tmcf_subst x (iter_lift i (Tmscf_snoc σ z)) -->* y.
  Proof.
    revert σ i nocc_0x.
    induction notneeded; intros σ i nocc_0x.
    - destruct (cf_iter_π₁idP_to_cf_iter_π₁id Hδ) as [j ?]; subst.
      destruct (lt_eq_lt_dec j i) as [[le_ji|eq_ji]|le_ij].
      + exists (Tmcf_ref j); intro z.
        eapply rt_trans.
        { onestep. apply cf_substπ₂. }
        eapply rt_trans.
        { eapply HINTcf_π₂_step_compatibility.
          apply Tmscf_compiterπid. }
        apply (cf_iter_π₂_lift _ _ le_ji).
      + subst.
        exfalso.
        apply nocc_0x.
        induction i.
        * repeat constructor.
        * constructor.
          assert (E:(S i = S i + 0)). {lia. } rewrite E at 1.
          apply Tmscf_OccurAtP_cf_iter_π₁.
      + destruct i.
        { destruct j.
          { exfalso. inversion le_ij. }
          exists (cf_iter_π₂ j σ); intro z.
          eapply rt_trans.
          { onestep. apply cf_substπ₂. }
          apply HINTcf_π₂_step_compatibility.
          eapply rt_trans.
          { apply Tmscf_compiterπid. }
          rewrite cf_iter_π₁_flip.
          apply AKcfσconv_iter_π₁_compatibility.
          onestep. apply cf_π₁beta.
        }
        exists (cf_iter_π₂ (Nat.pred (j-(S i))) (Tmscf_comp σ (cf_iter_π₁ (S i) Tmscf_id))); intro z.
        eapply rt_trans.
        { onestep. apply cf_substπ₂. }
        apply HINTcf_π₂_step_compatibility.
        eapply rt_trans.
        { apply Tmscf_compiterπid. }
        eapply rt_trans.
        { apply cf_iter_π₁_more_lift. exact le_ij. }
        eapply rt_trans.
        { eapply AKcfσconv_iter_π₁_compatibility.
          onestep. apply cf_snocomp. }
        assert (E: j - S i = S (Nat.pred (j - S i))). { lia. }
        rewrite E at 1.
        rewrite cf_iter_π₁_flip.
        eapply AKcfσconv_iter_π₁_compatibility.
        onestep. apply cf_π₁beta.
    - destruct (IHnotneeded1 σ i) as [xs redxs].
      {
        intro abs.
        apply nocc_0x.
        apply Tmcf_OccurP_rator.
        exact abs.
      }
      destruct (IHnotneeded2 σ i) as [ys redys].
      {
        intro abs.
        apply nocc_0x.
        apply Tmcf_OccurP_rand.
        exact abs.
      }
      exists (Tmcf_app xs ys); intro z.
      eapply rt_trans.
      { onestep. apply cf_appsubst.  }
      eapply rt_trans.
      { eapply HINTcf_rator_step_compatibility.
        apply redxs. }
      eapply HINTcf_rand_step_compatibility.
      apply redys.
    - destruct (IHnotneeded σ (S i))
        as [xs redxs].
      { intro abs.
        apply nocc_0x.
        constructor.
        exact abs. }
      exists (Tmcf_lam xs); intro z.
      eapply rt_trans.
      { onestep. apply cf_lamsubst. }
      eapply HINTcf_lam_step_compatibility.
      apply redxs.
  Qed.

  Local Lemma nocc_nsubst {x:Tmcf} {i:nat} (σ : Tmscf)
    (nocc_0x : ~ Tmcf_OccurP i x)
    : exists y,
      (Tmcf_subst x (iter_lift i σ) -->* y) /\
      (forall z, Tmcf_subst x (iter_lift i (Tmscf_snoc (Tmscf_π₁ σ) z)) -->* y).
  Proof.
    destruct (Tmcf_normalization x) as [x0 [xred nfx0]].
    destruct (nocc_nsubst'(i:=i) σ (Tmcfσnf_is_value nfx0)) as [y [red1y red2y]].
    { intro occ_0x0.
      apply nocc_0x.
      apply (Tmcf_Occur_compatibility_inv_tr xred occ_0x0). }
    exists y; split.
    + eapply rt_trans.
      { eapply HINTsubst_Tmcf_step_compatibility. exact xred. }
      exact red1y.
    + intro z.
      eapply rt_trans.
      { eapply HINTsubst_Tmcf_step_compatibility. exact xred. }
      apply red2y.
  Qed.

  Local Lemma nocc_nsubst_variant {x:Tmcf} {i:nat} (σ : Tmscf)
    (nocc_0x : ~ Tmcf_OccurP i x)
    : exists y, forall z,
      Tmcf_subst x (iter_lift i (Tmscf_snoc σ z)) -->* y.
  Proof.
    destruct (Tmcf_normalization x) as [x0 [xred nfx0]].
    destruct (nocc_nsubst_variant'(i:=i) σ (Tmcfσnf_is_value nfx0)) as [y redy].
    { intro occ_0x0.
      apply nocc_0x.
      apply (Tmcf_Occur_compatibility_inv_tr xred occ_0x0). }
    exists y; intro z.
    eapply rt_trans.
    { eapply HINTsubst_Tmcf_step_compatibility. exact xred. }
    apply redy.
  Qed.

  Lemma nocc_nsubst0 {x:Tmcf} (σ : Tmscf)
    (nocc_0x : ~ Tmcf_OccurP 0 x)
    : exists y,
      (Tmcf_subst x σ -->* y) /\
      (forall z, Tmcf_subst x (Tmscf_snoc (Tmscf_π₁ σ) z) -->* y).
  Proof.
    apply (nocc_nsubst (i:=0)); assumption.
  Qed.

  Lemma nocc_nsubst0_variant {x:Tmcf} (σ : Tmscf) (nocc_0x : ~ Tmcf_OccurP 0 x)
    : exists y, forall z,
      Tmcf_subst x (Tmscf_snoc σ z) -->* y.
  Proof.
    apply (nocc_nsubst_variant (i:=0)); assumption.
  Qed.

End nocc_nsubst0.