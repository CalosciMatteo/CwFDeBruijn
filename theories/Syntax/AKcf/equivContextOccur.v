From CwFdeBruijn.Syntax.AKcf Require Export occur context AKcf_Conv Conv_Lemmas nf_uniqueness.
From CwFdeBruijn.Syntax.Immersions Require Export dBToAKcf.

(* The following lemma state how
[cfcontext]/[cfassign] constraints [Tmcf_OccurP]/[Tmscf_OccurAtP] *)

Fixpoint contextToOccur {p:nat} {x: Tmcf} (ctx_x : cfcontext p x)
  : forall i, (Tmcf_OccurP i x) -> i < p
with assignToOccurAt {p q: nat} (δ:Tmscf) (ass_δ : cfassign p q δ)
  : (forall pos, pos < q -> forall i,
    (Tmscf_OccurAtP i pos δ) ->  i < p).
Proof.
{ intros i occ_ix.
  inversion ctx_x; subst.
  - inversion occ_ix; subst.
    refine (assignToOccurAt _ _ δ Hδ j _ _ occ_ijδ).
    apply (contextToOccur _ x0 Hx _ occ_jx).
  - inversion occ_ix; subst.
    refine (assignToOccurAt _ _ δ Hδ 0 _ _ occ_i0δ).
    lia.
  - inversion occ_ix; subst.
    + apply (contextToOccur _ x0 Hx _ occ_irator).
    + apply (contextToOccur _ y Hy _ occ_irand).
  - inversion occ_ix; subst.
    apply Nat.succ_lt_mono.
    apply (contextToOccur _ x0 H _ occ_ix0).
}
{ intros pos lt_posq i occ_ipδ.
  inversion ass_δ; subst.
  - inversion occ_ipδ; subst.
    + apply (contextToOccur _ x Hx _ occ_ix).
    + refine (assignToOccurAt _ _ δ0 Hδ _ _ _ occ_iδ).
      apply Nat.succ_lt_mono. exact lt_posq.
  - inversion occ_ipδ; subst.
    exact lt_posq.
  - inversion occ_ipδ; subst.
    refine (assignToOccurAt _ _ δ₂ Hδ₂ _ _ _ occ_ikδ₂).
    apply (assignToOccurAt _ _ δ₁ Hδ₁ _ lt_posq _ occ_kjδ₁).
  - inversion occ_ipδ; subst.
    refine (assignToOccurAt _ _ δ0 Hδ _ _ _ occ_δ).
    rewrite <-Nat.succ_lt_mono.
    exact lt_posq.
}
Qed.

Fixpoint assignTogelt {p q pos: nat} {δ:Tmscf}
  (ass_δ : cfassign p q δ) (lt_posq : q <= pos)
  : cf_iter_π₂ pos δ -->* Tmcf_ref ((pos + p)-q).
Proof.
  inversion ass_δ.
  - subst.
    destruct pos as [|pos].
    { solve_by_invert. }
    eapply rt_trans.
    { unfold cf_iter_π₂.
      rewrite cf_iter_π₁_flip.
      eapply HINTcf_π₂_step_compatibility.
      eapply AKcfσconv_iter_π₁_compatibility.
      onestep.
      apply cf_π₁beta. }
    apply (assignTogelt _ _ pos _ Hδ (le_S_n _ _ lt_posq)).
  - subst.
    assert (pos = pos + q - q). {lia. } destruct H.
    apply rt_refl.
  - subst.
    apply (Tmcfσstep_bwtr (x:= Tmcf_subst (cf_iter_π₂ pos δ₁) δ₂)).
    + apply Tmcf_ref_nf.
    + eapply rt_trans.
      { eapply HINTsubst_Tmcf_step_compatibility.
        apply (assignTogelt _ _ _ _ Hδ₁ lt_posq). }
      eapply rt_trans.
      { eapply rt_trans.
        { onestep. apply cf_substπ₂. }
        eapply HINTcf_π₂_step_compatibility.
        apply Tmscf_compiterπid. }
      assert (E: pos + p - q = pos +q0-q+p-q0). {lia. }
      rewrite E.
      apply (assignTogelt _ _ (pos + q0 - q) _ Hδ₂).
      lia.
    + eapply rt_trans.
      { onestep. apply cf_substπ₂. }
      eapply HINTcf_π₂_step_compatibility.
      apply Tmscf_compiterπ₁.
  - subst.
    unfold cf_iter_π₂.
    rewrite <-cf_iter_π₁_flip.
    assert (E: pos + p - q = S pos + p - S q). {lia. }
    rewrite E.
    apply (assignTogelt _ _ (S pos) _ Hδ).
    lia.
Qed.