From CwFdeBruijn.Syntax.AKcf Require Export AKcf_Conv.

(* the modus operandi for proving compatibility and its converse may be generalized *)

Lemma Tmcf_Occur_compatibility' {x y : Tmcf} {i:nat}
  (red: Tmcfσstep' x y) (H : Tmcf_OccurP i x)
  : Tmcf_OccurP i y.
Proof.
  inversion red; subst.
  - inversion H; subst.
    inversion occ_jx; subst.
    eapply Tmcf_OccurP_subst.
    + exact occ_jx0.
    + eapply Tmscf_OccurAtP_comp.
      * exact occ_ijδ.
      * exact occ_ijδ0.
  - inversion H; subst.
    inversion occ_i0δ; subst.
    exact occ_ix.
  - inversion H; subst.
    constructor.
    eapply Tmcf_OccurP_subst.
    + inversion occ_jx.
      apply occ_ix.
    + constructor.
      eapply Tmscf_OccurAtP_comp.
      * constructor.
        apply Tmscf_OccurAtP_id.
      * exact occ_ijδ.
  - inversion H; subst.
    inversion occ_jx; subst.
    constructor.
    econstructor.
    + apply occ_ijδ.
    + apply occ_i0δ.
  - inversion H; subst.
    + inversion occ_jx; subst.
      * apply Tmcf_OccurP_rator.
        econstructor; eassumption.
      * apply Tmcf_OccurP_rand.
        econstructor; eassumption.
Qed.

Lemma Tmcf_Occur_compatibility_inv' {x y : Tmcf} {i:nat}
  (red: Tmcfσstep' x y) (H : Tmcf_OccurP i y)
  : Tmcf_OccurP i x.
Proof.
  inversion red; subst.
  - inversion H; subst.
    inversion occ_ijδ; subst.
    repeat econstructor.
    + exact occ_jx.
    + exact occ_kjδ₁.
    + exact occ_ikδ₂.
  - repeat constructor.
    exact H.
  - inversion H; subst.
    inversion occ_ix; subst.
    inversion occ_ijδ; subst.
    + exfalso.
      solve_by_inverts 2.
    + inversion occ_iδ; subst.
      inversion occ_ikδ₂; subst.
      inversion occ_δ; subst.
      repeat econstructor.
      * exact occ_jx.
      * exact occ_kjδ₁.
  - inversion H; subst.
    inversion occ_i0δ; subst.
    repeat econstructor.
    + apply occ_kjδ₁.
    + apply occ_ikδ₂.
  - inversion H; subst.
    + inversion occ_irator; subst.
      econstructor.
      * apply Tmcf_OccurP_rator.
        eassumption.
      * eassumption.
    + inversion occ_irand; subst.
      econstructor.
      * apply Tmcf_OccurP_rand.
        eassumption.
      * eassumption.
Qed.

Lemma Tmscf_Occur_compatibility' {δ σ : Tmscf} {i pos:nat}
  (red: Tmscfσstep' δ σ) (H : Tmscf_OccurAtP i pos δ)
  : Tmscf_OccurAtP i pos σ.
Proof.
  inversion red; subst.
  - inversion H; subst.
    inversion occ_kjδ₁; subst.
    exact occ_ikδ₂.
  - inversion H; subst.
    inversion occ_ikδ₂; subst.
    exact occ_kjδ₁.
  - inversion H; subst.
    inversion occ_kjδ₁; subst.
    eapply Tmscf_OccurAtP_comp; [eapply Tmscf_OccurAtP_comp | idtac ].
    + apply occ_ikδ₂.
    + apply occ_ikδ₂0.
    + apply occ_kjδ₁0.
  - inversion H; subst.
    inversion occ_kjδ₁; subst.
    + apply Tmscf_OccurAtP_snocπ₂.
      eapply Tmcf_OccurP_subst.
      * exact occ_ix.
      * exact occ_ikδ₂.
    + apply Tmscf_OccurAtP_snocπ₁.
      eapply Tmscf_OccurAtP_comp.
      * exact occ_ikδ₂.
      * exact occ_iδ.
  - inversion H; subst.
    inversion occ_δ; subst.
    exact occ_iδ.
  - inversion H; subst.
    inversion occ_kjδ₁; subst.
    apply Tmscf_OccurAtP_π₁.
    eapply Tmscf_OccurAtP_comp.
    + exact occ_ikδ₂.
    + exact occ_δ.
  - inversion H; subst.
    + inversion occ_ix; subst.
      exact occ_i0δ.
    + inversion occ_iδ; subst.
      exact occ_δ.
Qed.

Lemma Tmscf_Occur_compatibility_inv' {δ σ : Tmscf} {i pos:nat}
  (red: Tmscfσstep' δ σ) (H : Tmscf_OccurAtP i pos σ)
  : Tmscf_OccurAtP i pos δ.
Proof.
  inversion red; subst.
  - econstructor.
    + exact H.
    + constructor.
  - econstructor.
    + constructor.
    + exact H.
  - inversion H; subst.
    inversion occ_ikδ₂; subst.
    repeat econstructor; eassumption.
  - inversion H; subst.
    + inversion occ_ix; subst.
      repeat econstructor; eassumption.
    + inversion occ_iδ; subst.
      repeat econstructor; eassumption.
  - repeat econstructor; assumption.
  - inversion H; subst.
    inversion occ_δ; subst.
    repeat econstructor; eassumption.
  - destruct pos.
    + apply Tmscf_OccurAtP_snocπ₂.
      constructor; assumption.
    + apply Tmscf_OccurAtP_snocπ₁.
      constructor; assumption.
Qed.

Fixpoint Tmcf_Occur_compatibility {x y : Tmcf} {i:nat}
  (red: Tmcfσstep x y) (occ_ix : Tmcf_OccurP i x)
  : Tmcf_OccurP i y
with Tmscf_Occur_compatibility {δ σ : Tmscf} {i pos:nat}
  (red: Tmscfσstep δ σ) (occ_ipδ : Tmscf_OccurAtP i pos δ)
  : Tmscf_OccurAtP i pos σ.
Proof.
{ revert i occ_ix.
  dependent induction red; intros i occ_ix.
  - apply (Tmcf_Occur_compatibility' H occ_ix).
  - inversion occ_ix; subst.
    econstructor.
    + apply (IHred _ occ_jx).
    + exact occ_ijδ.
  - inversion occ_ix; subst.
    econstructor.
    + exact occ_jx.
    + eapply Tmscf_Occur_compatibility.
      * exact H.
      * exact occ_ijδ.
  - inversion occ_ix; subst.
    constructor.
    eapply Tmscf_Occur_compatibility.
    * exact H.
    * exact occ_i0δ.
  - inversion occ_ix; subst.
    + apply Tmcf_OccurP_rator.
      apply (IHred _ occ_irator).
    + apply Tmcf_OccurP_rand.
      exact occ_irand.
  - inversion occ_ix; subst.
    + apply Tmcf_OccurP_rator.
      exact occ_irator.
    + apply Tmcf_OccurP_rand.
      apply (IHred _ occ_irand).
  - inversion occ_ix; subst.
    constructor.
    apply (IHred _ occ_ix0).
}
{ revert i pos occ_ipδ.
  dependent induction red; intros i pos occ_ipδ.
  - apply (Tmscf_Occur_compatibility' H).
    exact occ_ipδ.
  - inversion occ_ipδ; subst; constructor.
    + exact occ_ix.
    + apply (IHred _ _ occ_iδ).
  - inversion occ_ipδ; subst; constructor.
    + apply (Tmcf_Occur_compatibility _ _ _ H occ_ix).
    + exact occ_iδ.
  - inversion occ_ipδ; subst; econstructor.
    + exact occ_ikδ₂.
    + apply (IHred _ _ occ_kjδ₁).
  - inversion occ_ipδ; subst; econstructor.
    + apply (IHred _ _ occ_ikδ₂).
    + exact occ_kjδ₁.
  - inversion occ_ipδ; subst; constructor.
    apply (IHred _ _ occ_δ).
}
Qed.

Fixpoint Tmcf_Occur_compatibility_inv {x y : Tmcf} {i:nat}
  (red: Tmcfσstep x y) (occ_iy : Tmcf_OccurP i y)
  : Tmcf_OccurP i x
with Tmscf_Occur_compatibility_inv {δ σ : Tmscf} {i pos:nat}
  (red: Tmscfσstep δ σ) (occ_ipσ : Tmscf_OccurAtP i pos σ)
  : Tmscf_OccurAtP i pos δ.
Proof.
{ revert i occ_iy.
  dependent induction red; intros i occ_iy.
  - apply (Tmcf_Occur_compatibility_inv' H occ_iy).
  - inversion occ_iy; subst.
    econstructor.
    + apply (IHred _ occ_jx).
    + exact occ_ijδ.
  - inversion occ_iy; subst.
    econstructor.
    + exact occ_jx.
    + eapply Tmscf_Occur_compatibility_inv.
      * exact H.
      * exact occ_ijδ.
  - inversion occ_iy; subst.
    constructor.
    eapply Tmscf_Occur_compatibility_inv.
    * exact H.
    * exact occ_i0δ.
  - inversion occ_iy; subst.
    + apply Tmcf_OccurP_rator.
      apply (IHred _ occ_irator).
    + apply Tmcf_OccurP_rand.
      exact occ_irand.
  - inversion occ_iy; subst.
    + apply Tmcf_OccurP_rator.
      exact occ_irator.
    + apply Tmcf_OccurP_rand.
      apply (IHred _ occ_irand).
  - inversion occ_iy; subst.
    constructor.
    apply IHred.
    assumption.
}
{ revert i pos occ_ipσ.
  dependent induction red; intros i pos occ_ipσ.
  - apply (Tmscf_Occur_compatibility_inv' H).
    exact occ_ipσ.
  - inversion occ_ipσ; subst; constructor.
    + exact occ_ix.
    + apply (IHred _ _ occ_iδ).
  - inversion occ_ipσ; subst; constructor.
    + apply (Tmcf_Occur_compatibility_inv _ _ _ H occ_ix).
    + exact occ_iδ.
  - inversion occ_ipσ; subst; econstructor.
    + exact occ_ikδ₂.
    + apply (IHred _ _ occ_kjδ₁).
  - inversion occ_ipσ; subst; econstructor.
    + apply (IHred _ _ occ_ikδ₂).
    + exact occ_kjδ₁.
  - inversion occ_ipσ; subst; constructor.
    apply (IHred _ _ occ_δ).
}
Qed.

Lemma Tmcf_Occur_compatibility_iff {x y : Tmcf} {i:nat}
  (red: Tmcfσstep x y)
  : (Tmcf_OccurP i x) <-> (Tmcf_OccurP i y).
Proof.
  split.
  - apply (Tmcf_Occur_compatibility red).
  - apply (Tmcf_Occur_compatibility_inv red).
Qed.

Lemma Tmcf_Occur_compatibility_tr {x y : Tmcf} {i:nat}
  (red: x -->* y) (occ_ix : Tmcf_OccurP i x)
  : Tmcf_OccurP i y.
Proof.
  dependent induction red.
  - apply (Tmcf_Occur_compatibility H occ_ix).
  - exact occ_ix.
  - apply IHred2.
    apply IHred1.
    exact occ_ix.
Qed.

Lemma Tmcf_Occur_compatibility_inv_tr {x y : Tmcf} {i:nat}
  (red: x -->* y) (occ_iy : Tmcf_OccurP i y)
  : Tmcf_OccurP i x.
Proof.
  dependent induction red.
  - apply (Tmcf_Occur_compatibility_inv H occ_iy).
  - exact occ_iy.
  - apply IHred1.
    apply IHred2.
    exact occ_iy.
Qed.

Lemma Tmscf_Occur_compatibility_inv_tr  {δ σ : Tmscf} {i pos:nat}
  (red: δ --s>* σ) (occ_ipσ : Tmscf_OccurAtP i pos σ)
  : Tmscf_OccurAtP i pos δ.
Proof.
  dependent induction red.
  - apply (Tmscf_Occur_compatibility_inv H occ_ipσ).
  - exact occ_ipσ.
  - apply IHred1.
    apply IHred2.
    exact occ_ipσ.
Qed.