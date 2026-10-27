From CwFdeBruijn.Syntax.AKcf Require Export context context_Conv AKcf_Conv Conv_Lemmas values normalization.

Lemma cfassign_cf_iter_π₁idP {p q} (δ : Tmscf) (ass : cfassign p q δ) (H : cf_iter_π₁idP δ)
  : p >= q /\ δ = cf_iter_π₁ (p - q) Tmscf_id.
Proof.
  destruct (cf_iter_π₁idP_to_cf_iter_π₁id H) as [p' ?]; subst.
  revert H. intros _.
  revert p q ass.
  induction p'; intros p q ass.
  - cbn in ass.
    inversion ass; subst.
    split.
    + lia.
    + f_equal. lia.
  - inversion ass; subst.
    specialize (IHp' _ _ Hδ) as [ge eq].
    split.
    + lia.
    + change (cf_iter_π₁ (S p') Tmscf_id) with (Tmscf_π₁ (cf_iter_π₁ p' Tmscf_id)).
      rewrite eq.
      change (Tmscf_π₁ (cf_iter_π₁ (p - S q) Tmscf_id)) with
        (cf_iter_π₁ (S (p - S q)) Tmscf_id).
      f_equal.
      lia.
Qed.

Lemma cfeval_ge_V {p q} (δ : Tmscf) (ass: cfassign p q δ) i (ge : i >= q) (δV : Tmscfσvalue δ):
(cf_iter_π₁ i δ) <--s>*
(cf_iter_π₁ (i - q + p) Tmscf_id).
Proof.
  revert i q ge ass.
  induction δV; intros i q ge ass; subst.
  - specialize (cfassign_cf_iter_π₁idP δ ass Hδ) as [ge_pq ?]; subst.
    rewrite Tmscf_nestediterπ₁.
    apply rst_refl_propositional.
    f_equal.
    lia.
  - inversion ass; subst.
    destruct i. {lia. }
    change (S i - S q0 + p) with (i - q0 + p).
    eapply rst_trans.
    2:{ apply IHδV.
      - lia.
      - exact Hδ. }
    apply clos_rt_clos_rst.
    rewrite cf_iter_π₁_flip.
    apply AKcfσconv_iter_π₁_compatibility.
    auto with AKcf sets.
Qed.

Lemma cfeval_ge {p q} (δ : Tmscf) (ass: cfassign p q δ) i (ge : i >= q) :
(cf_iter_π₁ i δ) <--s>*
(cf_iter_π₁ (i - q + p) Tmscf_id).
Proof.
  destruct (Tmscf_normalization δ) as [δ0 [δ_red δ0_nf]].
  eapply rst_trans.
  { apply clos_rt_clos_rst.
    apply AKcfσconv_iter_π₁_compatibility.
    exact δ_red. }
  apply cfeval_ge_V.
  - apply (cfassign_preserved δ_red ass).
  - exact ge.
  - apply (Tmscfσnf_is_value _ δ0_nf).
Qed.