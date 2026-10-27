From CwFdeBruijn.Syntax.AKcf Require Import values Conv_Lemmas.
From Stdlib Require Import Bool.
Section Lemmas.

  Lemma normalizeσTmcfvalue {x : Tmcf} (xV : Tmcfσvalue x) : normalize Tmcfσstep x.
  Proof.
    apply normalize_refl.
    apply Tmcfσvalue_is_nf.
    apply xV.
  Qed.

  Lemma normalizeσTmscfvalue {δ : Tmscf} (δV : Tmscfσvalue δ) : normalize Tmscfσstep δ.
  Proof.
    apply normalize_refl.
    apply Tmscfσvalue_is_nf.
    apply δV.
  Qed.

  Lemma normalizeσapp {x y : Tmcf}
    (xN: normalize Tmcfσstep x) (yN: normalize Tmcfσstep y) : normalize Tmcfσstep (Tmcf_app x y).
  Proof.
    destruct xN as [x' [xred xnf]].
    destruct yN as [y' [yred ynf]].
    eapply normalize_trans.
    { eapply rt_trans.
      { eapply HINTcf_rator_step_compatibility.
        exact xred. }
      eapply HINTcf_rand_step_compatibility.
      exact yred.
    }
    apply normalize_refl.
    apply Tmcfσvalue_is_nf.
    apply Tmcfσvalue_app; apply Tmcfσnf_is_value;
    assumption.
  Qed.

  Lemma normalizeσsubstlam {x : Tmcf} {δ : Tmscf}
    (H : normalize Tmcfσstep (Tmcf_subst x (lift δ)))
  : normalize Tmcfσstep (Tmcf_subst (Tmcf_lam x) δ).
  Proof.
    destruct H as [z [redz znf]].
    eapply normalize_trans.
    { apply rt_step. apply cf_refl. apply cf_lamsubst. }
    split with (Tmcf_lam z); split.
    { fold Tmcfσconv. auto with AKcf sets. }
    apply Tmcfσvalue_is_nf.
    apply Tmcfσvalue_lam.
    apply Tmcfσnf_is_value.
    exact znf.
  Qed.

  Lemma normalizeσsubstπ₂ {δ σ: Tmscf}
    (H : normalize Tmcfσstep (Tmcf_π₂ (Tmscf_comp δ σ)))
  : normalize Tmcfσstep (Tmcf_subst (Tmcf_π₂ δ) σ).
  Proof.
    destruct H as [z [redz znf]].
    eapply normalize_trans.
    { apply rt_step. apply cf_refl. apply cf_substπ₂. }
    split with z; split.
    { fold Tmcfσconv. auto with AKcf sets. }
    apply znf.
  Qed.

  Lemma normalizeσsubst_compatibility {x:Tmcf} {δ σ: Tmscf}
    (H1 : δ --s>* σ)
    (H2 : normalize Tmcfσstep (Tmcf_subst x σ))
    : normalize Tmcfσstep (Tmcf_subst x δ).
  Proof.
    eapply normalize_trans with (Tmcf_subst x σ).
    - fold Tmcfσconv. auto with AKcf sets.
    - exact H2.
  Qed.

  Lemma normalizeσsubstsubst {x : Tmcf} {δ1 δ2 : Tmscf} (H : normalize Tmcfσstep (Tmcf_subst x (Tmscf_comp δ1 δ2)))
    : normalize Tmcfσstep (Tmcf_subst (Tmcf_subst x δ1) δ2).
  Proof.
    refine (normalize_trans _ _ _ _ H).
    auto with AKcf sets.
  Qed.

  Lemma normalizeσsnoc {x:Tmcf} (xN : normalize Tmcfσstep x)
    {δ: Tmscf} (δN : normalize Tmscfσstep δ)
    : normalize Tmscfσstep (Tmscf_snoc δ x).
  Proof.
    destruct xN as [x' [xred xnf]].
    destruct δN as [δ' [δred δnf]].
    eapply normalize_trans with (Tmscf_snoc δ' x).
    { fold Tmscfσconv; auto with AKcf sets. }
    eapply normalize_trans with (Tmscf_snoc δ' x').
    { fold Tmscfσconv; auto with AKcf sets. }
    destruct (reflect_dec _ _ (etaRelated_spec δ' x')).
    - destruct (etaRelatedP_tosig e) as [ι [? ?]]; subst.
      exists ι.
      split.
      { fold Tmscfσconv; auto with AKcf sets. }
      intros [ι' red].
      apply δnf.
      exists (Tmscf_π₁ ι').
      auto with AKcf sets.
    - split with (Tmscf_snoc δ' x'); split.
      { fold Tmscfσconv; auto with AKcf sets. }
      apply Tmscfσvalue_is_nf.
      apply Tmscfσvalue_snoc.
      + apply Tmscfσnf_is_value.
        exact δnf.
      + apply Tmcfσnf_is_value.
        exact xnf.
      + exact n.
  Qed.

  Lemma normalizeσsnocomp {x:Tmcf}
    {δ σ: Tmscf} (Hc : normalize Tmscfσstep (Tmscf_comp δ σ))
    (Hs : normalize Tmcfσstep (Tmcf_subst x σ))
    : normalize Tmscfσstep (Tmscf_comp (Tmscf_snoc δ x) σ).
  Proof.
    eapply normalize_trans.
    { apply rt_step. apply cf_srefl. apply cf_snocomp. }
    apply normalizeσsnoc; assumption.
  Qed.

  Lemma normalizeσcomplid {δ:Tmscf} (H : normalize Tmscfσstep δ)
    : normalize Tmscfσstep (Tmscf_comp Tmscf_id δ).
  Proof.
    eapply normalize_trans with δ.
    - fold Tmscfσconv. auto with AKcf sets.
    - exact H.
  Qed.

  Lemma cf_iter_π₁_normalization (δ : Tmscf) (δV : Tmscfσvalue δ) (i:nat) : normalize Tmscfσstep (cf_iter_π₁ i δ).
  Proof.
    revert i.
    induction δV; intro i.
    - destruct (cf_iter_π₁idP_to_cf_iter_π₁id H) as [j ?];
      subst.
      split with (cf_iter_π₁ (i+j) Tmscf_id).
      split.
      + rewrite Tmscf_nestediterπ₁.
        apply rt_refl.
      + apply Tmscfσvalue_is_nf.
        apply Tmscfσvalue_iterπ₁id.
        apply Tmscfσvalue_cf_iter_π₁id.
    - induction i as [| i IHi].
      + split with (Tmscf_snoc δ y).
        split.
        * simpl. auto with AKcf sets.
        * apply Tmscfσvalue_is_nf.
          apply (Tmscfσvalue_snoc δV H).
          apply H0.
      + destruct (IHδV i) as [ν Hν].
        split with ν.
        split.
        * rewrite cf_iter_π₁_flip.
          eapply (rt_trans _ Tmscfσstep _ (cf_iter_π₁ i δ)).
          {
            apply AKcfσconv_iter_π₁_compatibility.
            auto with AKcf sets. }
          apply Hν.
        * apply Hν.
    Qed.

  Lemma Tmcf_π₂_normalization (δ : Tmscf) (δV : Tmscfσvalue δ) : normalize Tmcfσstep (Tmcf_π₂ δ).
  Proof.
    induction δV; subst.
    - destruct (cf_iter_π₁idP_to_cf_iter_π₁id H) as [i ?]; subst.
      esplit with (Tmcf_ref i); split.
      + auto with AKcf sets.
      + apply Tmcf_ref_nf.
    - esplit with y; split.
      + auto with AKcf sets.
      + apply Tmcfσvalue_is_nf.
        exact H.
  Qed.

  Lemma normalizeσπ₂ (δ : Tmscf) (δN : normalize Tmscfσstep δ) : normalize Tmcfσstep (Tmcf_π₂ δ).
  Proof.
    destruct δN as [δ' [δred δnf]].
    eapply normalize_trans with (Tmcf_π₂ δ').
    - fold Tmcfσconv; auto 2 with AKcf sets.
    - apply Tmcf_π₂_normalization.
      apply Tmscfσnf_is_value.
      exact δnf.
  Qed.

  Lemma normalizeσπ₁ (δ : Tmscf) (δN : normalize Tmscfσstep δ) : normalize Tmscfσstep (Tmscf_π₁ δ).
  Proof.
    destruct δN as [δ' [δred δnf]].
    eapply normalize_trans with (Tmscf_π₁ δ').
    - apply HINTcf_π₁_step_compatibility.
      exact δred.
    - eapply (cf_iter_π₁_normalization _ _ 1).
      Unshelve.
      apply Tmscfσnf_is_value.
      exact δnf.
  Qed.

  Lemma cf_iter_π₂_normalization (δ : Tmscf) (δV : Tmscfσvalue δ) (i:nat) : normalize Tmcfσstep (cf_iter_π₂ i δ).
  Proof.
    apply normalizeσπ₂.
    apply cf_iter_π₁_normalization.
    exact δV.
  Qed.

  Lemma cf_comp_iterπ₁id_normalization (i:nat) (σ : Tmscf) (Hσ : normalize Tmscfσstep σ)
    : normalize Tmscfσstep (Tmscf_comp (cf_iter_π₁ i Tmscf_id) σ).
  Proof.
    destruct Hσ as [σ' [σred σ_nf]].
    apply normalize_trans with (Tmscf_comp (cf_iter_π₁ i Tmscf_id) σ').
    { autored. }
    apply Tmscfσnf_is_value in σ_nf.
    destruct (cf_iter_π₁_normalization σ' σ_nf i) as [ν Hν].
    split with ν; split.
    - eapply (rt_trans _ (Tmscfσstep) _ (cf_iter_π₁ i σ')).
      { apply Tmscf_compiterπid. }
      apply Hν.
    - apply Hν.
  Qed.

  Lemma Tmscfσvalueπ₁normalize {δ: Tmscf} (δV : Tmscfσvalue δ)  : normalize Tmscfσstep (Tmscf_π₁ δ).
  Proof.
    refine (cf_iter_π₁_normalization _ _ 1).
    exact δV.
  Qed.

  Lemma Tmscfσvalueπ₂normalize {δ: Tmscf} (δV : Tmscfσvalue δ)  : normalize Tmcfσstep (Tmcf_π₂ δ).
  Proof.
    apply normalizeσπ₂.
    apply normalize_refl.
    apply Tmscfσvalue_is_nf.
    exact δV.
  Qed.

End Lemmas.

Section CountingLam.

  (* we assume here substitution does not generate new lambda,
    this will be true for our usecase of finitary renamings *)
  Fixpoint nlamsInTmcfσValue (x :Tmcf) : nat :=
  match x with
    | Tmcf_subst x _δ => (nlamsInTmcfσValue x)
    | Tmcf_π₂ δ => 0
    | Tmcf_app x y => (nlamsInTmcfσValue x) + (nlamsInTmcfσValue y)
    | Tmcf_lam x => S (nlamsInTmcfσValue x)
  end.

  (* The goal is to prove [[normalize Tmcfσstep (Tmcf_subst x δ)]]
    for finitary renamings, that is substitution closed under
    - [[π₁^i Tmscf_id]]
    - snoc with [[Tmcf_ref j]].
  *)

  (* This make sense only for the [[Renaming]] substitution defined below *)
  Fixpoint lift_reduct (δ : Tmscf) : Tmscf :=
  match δ with
  | Tmscf_snoc δ x => Tmscf_snoc (lift_reduct δ) match x with
    | Tmcf_π₂ σ => Tmcf_π₂ (Tmscf_π₁ σ)
    | _ => x (* arbitrary, only [[Tmcf_π₂]] appear in [[Renaming]] substitutions *)
    end
  | Tmscf_id => Tmscf_π₁ Tmscf_id
  | Tmscf_comp δ1 δ2 => Tmscf_comp δ1 (lift_reduct δ2) (* this is arbitrary,
      composition will never occour in [[Renaming]] substitutions *)
  | Tmscf_π₁ δ => Tmscf_π₁ (Tmscf_π₁ δ)
  end.

  Lemma lift_cf_iter_π₁id j : (lift_reduct (cf_iter_π₁ j Tmscf_id)) = (cf_iter_π₁ (S j) Tmscf_id).
  Proof.
    induction j; reflexivity.
  Qed.

  Lemma cf_iter_π₁idP_lift j : cf_iter_π₁idP (lift_reduct (cf_iter_π₁ j Tmscf_id)).
  Proof.
    rewrite lift_cf_iter_π₁id.
    apply Tmscfσvalue_cf_iter_π₁id.
  Qed.

  Lemma Tmscfσvalue_lift {δ : Tmscf} (δV : Tmscfσvalue δ) : Tmscfσvalue (lift_reduct δ).
  Proof.
    induction δV.
    - apply Tmscfσvalue_iterπ₁id.
      destruct (cf_iter_π₁idP_to_cf_iter_π₁id Hδ) as [i ?]; subst.
      apply cf_iter_π₁idP_lift.
    - destruct x.
      2:{cbn.
        apply (Tmscfσvalue_snoc IHδV).
        - inversion Hx; subst.
          apply Tmcfσvalue_π₂.
          constructor.
          exact Hδ.
        - apply (elimF (etaRelated_spec (lift_reduct δ) _)).
          destruct δ; try reflexivity.
          cbn.
          unfold Tmscf_beq.
          cbn.
          destruct (deceq_Tmscf δ δ0); subst.
          + exfalso.
            apply Hη.
            constructor.
          + reflexivity. }
      all: cbn.
      all: apply Tmscfσvalue_snoc; try assumption.
      all: apply (elimF (etaRelated_spec (lift_reduct δ) _)).
      all: destruct (lift_reduct δ); reflexivity.
  Qed.

  (*TODO: this should be called (finitary) [Renamings]*)
  Inductive Renaming : Tmscf -> Prop :=
  | Renaming_cf_iter_π₁id {δ} (Hδ: cf_iter_π₁idP δ)
    : Renaming (δ)
  | Renaming_snocref
    {δ} (Hδ : Renaming δ)
    {x} (Hx : TmcfσisrefP x)
    : Renaming (Tmscf_snoc δ x).

  Fixpoint Renamingb (δ: Tmscf) :  bool :=
  match δ with
  | Tmscf_snoc δ x => Renamingb δ && Tmcfσisrefb x
  | Tmscf_id => true
  | Tmscf_comp δ σ => false
  | Tmscf_π₁ δ => cf_iter_π₁idb δ
  end.

  Theorem Renaming_spec (δ: Tmscf) : reflect (Renaming δ) (Renamingb δ).
  Proof.
    induction δ.
    - apply (equivP (P:=(Renaming δ /\ TmcfσisrefP x))).
      + apply (andPP IHδ).
        apply Tmcfσisref_spec.
      + split.
        * intros [ Hδ Hx].
          inversion Hx; subst.
          apply (Renaming_snocref).
          all: assumption.
        * intro H.
          inversion H; subst; try solve_by_invert.
          split; assumption.
    - apply ReflectT.
      apply Renaming_cf_iter_π₁id.
      apply cf_iter_π₁idP_id.
    - apply ReflectF.
      intro H.
      inversion H.
      try solve_by_invert.
    - apply (equivP (P:=(cf_iter_π₁idP δ))).
      + apply cf_iter_π₁id_spec.
      + split.
        * intro H.
          constructor.
          constructor.
          apply H.
        * intro H.
          inversion H; subst.
          inversion Hδ; subst.
          assumption.
  Qed.

  Definition Renaming_rect
    (P : Tmscf -> Type)
    (X1 : forall δ : Tmscf, cf_iter_π₁idP δ -> P δ)
    (X2 : forall δ : Tmscf, Renaming δ -> P δ ->
          forall x : Tmcf, TmcfσisrefP x ->
            P (Tmscf_snoc δ x))
    (δ : Tmscf) (H : Renaming δ)
    : P δ.
  Proof.
    assert (E := (proj1 (reflect_iff _ _ (Renaming_spec _)) H)).
    induction δ; try discriminate E.
    - simpl in E.
      destruct (andP E) as [UDCδ xV].
      apply X2.
      + apply (reflect_iff _ _ (Renaming_spec δ)).
        exact UDCδ.
      + apply IHδ.
        * apply (reflect_iff _ _ (Renaming_spec δ)).
          exact UDCδ.
        * exact UDCδ.
      + apply (reflect_iff _ _ (Tmcfσisref_spec x)).
        exact xV.
    - apply X1.
      constructor.
    - apply X1.
      inversion H.
      exact Hδ.
  Qed.

  Definition Renaming_rec := Renaming_rect.

  Lemma Renaming_lift_reduct {δ: Tmscf} (H:Renaming δ)
    : Renaming (lift_reduct δ).
  Proof.
    dependent induction H.
    - apply Renaming_cf_iter_π₁id.
      destruct (cf_iter_π₁idP_to_cf_iter_π₁id Hδ) as [j ?]; subst.
      destruct j.
      apply cf_iter_π₁idP_π₁.
      --apply cf_iter_π₁idP_id.
      --apply cf_iter_π₁idP_lift.
    - apply Renaming_snocref.
      + apply IHRenaming.
      + inversion Hx.
        apply Tmcfσisref_ref.
        apply cf_iter_π₁idP_π₁.
        apply Hδ.
  Qed.

  Lemma RenamingnotComp {δ1 δ2: Tmscf} (H : Renaming (Tmscf_comp δ1 δ2)) : False.
  Proof.
    solve_by_inverts 2.
  Qed.

  Lemma Renaming_caseπ₁ {δ} (H:Renaming (Tmscf_π₁ δ))
    : { i & δ = cf_iter_π₁ i Tmscf_id}.
  Proof.
    apply cf_iter_π₁idP_to_cf_iter_π₁id.
    inversion H.
    inversion Hδ.
    exact Hδ0.
  Qed.

  Lemma π₁Renaming (δ : Tmscf) (x : Tmcf) (H : Renaming (Tmscf_snoc δ x))
    : Renaming δ.
  Proof.
    inversion H.
    - solve_by_invert.
    - assumption.
  Qed.

  Lemma π₂Renaming {δ : Tmscf} {x : Tmcf} (Hδ : Renaming (Tmscf_snoc δ x))
    : { i & x = Tmcf_ref i}.
  Proof.
    apply TmcfσisrefP_tosig.
    inversion Hδ.
    - inversion Hδ0.
    - exact Hx.
  Qed.

  Lemma Renamingcompπ₁ {δ : Tmscf} (H : Renaming δ): Tmscf_comp δ (Tmscf_π₁ Tmscf_id) --s>* lift_reduct δ.
  Proof.
    revert H; induction δ; intro H.
    - eapply rt_trans.
      { apply rt_step.
        apply cf_srefl.
        apply cf_snocomp. }
      eapply rt_trans.
      + eapply HINTsnoc_Tmscf_step_compatibility.
        apply IHδ.
        eapply π₁Renaming.
        apply H.
      + eapply HINTsnoc_Tmcf_step_compatibility.
        destruct (π₂Renaming H); subst.
        simpl.
        apply Tmcf_substliftref.
    - auto with AKcf sets.
    - exfalso.
      eapply (RenamingnotComp H).
    - destruct (Renaming_caseπ₁ H) as [i ?]; subst.
      simpl.
      change (Tmscf_comp (cf_iter_π₁ (S i) Tmscf_id) (cf_iter_π₁ 1 Tmscf_id) --s>* cf_iter_π₁ ((S (S i))) Tmscf_id).
      assert (E: S (S i) = S i + 1). { lia. }
      rewrite E.
      apply Tmscf_compiterπids.
  Qed.

  Lemma Renaming_lift {δ : Tmscf} (H : Renaming δ)
    : { σ | (lift δ) --s>* σ /\ (Renaming σ)}.
  Proof.
    exists (Tmscf_snoc (lift_reduct δ) (Tmcf_π₂ Tmscf_id)).
    split.
    - apply HINTsnoc_Tmscf_step_compatibility.
      apply Renamingcompπ₁.
      exact H.
    - apply Renaming_snocref.
      + apply (Renaming_lift_reduct H).
      + apply Tmcfσisref_ref.
        apply cf_iter_π₁idP_id.
  Qed.

  Lemma Tmscfσvalue_Renaming {δ : Tmscf} (H : Renaming δ)
    : normalize Tmscfσstep δ.
  Proof.
    dependent induction H.
    - apply normalizeσTmscfvalue.
      apply Tmscfσvalue_iterπ₁id.
      exact H.
    - apply normalizeσsnoc.
      * apply normalizeσTmcfvalue.
        apply Tmcfσvalue_ref'.
        exact H0.
      * assumption.
  Qed.

  Lemma Tmscf_π₁Renaming {δ : Tmscf} (H : Renaming δ)
  :  {ν | (Tmscf_π₁ δ) --s>* ν /\ Renaming ν}.
  Proof.
    induction H.
    - split with (Tmscf_π₁ δ); split.
      { apply rt_refl. }
      repeat constructor.
      exact H.
    - split with δ; split.
      { auto with AKcf sets. }
      exact H.
  Qed.

  Lemma Renaming_cf_iter_π₁id' i : Renaming (cf_iter_π₁ i Tmscf_id).
  Proof.
    apply Renaming_cf_iter_π₁id.
    apply Tmscfσvalue_cf_iter_π₁id.
  Qed.

  Lemma Tmscf_iterπ₁Renaming {δ : Tmscf} {i:nat} (H : Renaming δ)
  :  {ν | (cf_iter_π₁ i δ) --s>* ν /\ Renaming ν}.
  Proof.
    induction i.
    - exists δ; auto with AKcf sets.
    - destruct (IHi) as [ν [redν UDCν]].
      destruct (Tmscf_π₁Renaming UDCν) as [τ Hτ].
      exists τ; split.
      { eapply rt_trans.
        eapply HINTcf_π₁_step_compatibility.
        exact redν.
        apply Hτ. }
      apply Hτ.
  Qed.

  Lemma Tmscf_π₂Renaming {δ : Tmscf} (H : Renaming δ)
  : {x : Tmcf | (Tmcf_π₂ δ) -->* x /\ TmcfσisrefP x}.
  Proof.
    induction H.
    - exists (Tmcf_π₂ δ).
      split.
      { auto with AKcf sets. }
      constructor.
      assumption.
    - split with x; auto 6 with AKcf sets.
  Qed.

  Lemma refsubstUDC (i: nat) {δ: Tmscf}
    (UDCδ : Renaming δ)
    : {x : Tmcf | (Tmcf_subst (Tmcf_ref i) δ) -->* x
                  /\ TmcfσisrefP x}.
  Proof.
    destruct (Tmscf_iterπ₁Renaming (i:=i) (δ:= δ) UDCδ) as [ν [redν UDCν]].
    destruct (Tmscf_π₂Renaming (δ:=ν) UDCν) as [τ Hτ].
    exists τ; split.
    - eapply rt_trans.
      { eapply rt_trans.
        { onestep. apply cf_substπ₂.  }
        eapply HINTcf_π₂_step_compatibility.
        eapply rt_trans.
        { apply Tmscf_compiterπid. }
        exact redν.
      }
      apply Hτ.
    - apply Hτ.
  Qed.

  Lemma compRenaming {δ σ : Tmscf}
    (UDCδ : Renaming δ)
    (UDCσ : Renaming σ)
    : { ν |
      Tmscf_comp δ σ
      --s>* ν /\ Renaming ν}.
  Proof.
    revert σ UDCσ.
    dependent induction UDCδ.
    - dependent induction H; intros σ UDCσ.
      + exists σ; split.
        * auto with AKcf sets.
        * exact UDCσ.
      + destruct (IHcf_iter_π₁idP σ UDCσ)
          as [δσ [redδσ UDCδσ]].
        destruct (Tmscf_π₁Renaming UDCδσ)
          as [ν [redν UDCν]].
        exists ν; split.
        * eapply rt_trans.
          { onestep. apply cf_π₁comp. }
          eapply rt_trans.
          { eapply HINTcf_π₁_step_compatibility.
            exact redδσ. }
          exact redν.
        * exact UDCν.
    - intros σ UDCσ.
      destruct (IHUDCδ σ UDCσ) as [ν [redν UDCν]].
      destruct (TmcfσisrefP_tosig H) as [i ?]; subst.
      destruct (refsubstUDC i UDCσ) as [y [redy isref_y]].
      exists (Tmscf_snoc ν y); split.
      + eapply rt_trans. { onestep. apply cf_snocomp. }
        eapply rt_trans.
        * eapply HINTsnoc_Tmcf_step_compatibility.
          exact redy.
        * eapply HINTsnoc_Tmscf_step_compatibility.
          exact redν.
      + apply Renaming_snocref.
        * exact UDCν.
        * exact isref_y.
  Qed.

  Lemma normalizeσsubstπ₂Renaming {σ : Tmscf} (Hδ : cf_iter_π₁idP σ) {δ : Tmscf} (H : Renaming δ)
    : normalize Tmcfσstep (Tmcf_subst (Tmcf_π₂ σ) δ).
  Proof.
    apply normalizeσsubstπ₂.
    apply normalizeσπ₂.
    destruct (cf_iter_π₁idP_to_cf_iter_π₁id Hδ); subst.
    apply cf_comp_iterπ₁id_normalization.
    apply Tmscfσvalue_Renaming.
    apply H.
  Qed.

  Lemma normalizeσsubstapp
  {x:Tmcf} {y:Tmcf} {δ : Tmscf}
  (Hx : normalize Tmcfσstep (Tmcf_subst x δ))
  (Hy : normalize Tmcfσstep (Tmcf_subst y δ))
  : normalize Tmcfσstep (Tmcf_subst (Tmcf_app x y) δ).
  Proof.
    destruct Hx as [x0 [redx nfx0]].
    destruct Hy as [y0 [redy nfy0]].
    eapply normalize_trans.
    { eapply rt_trans.
      { onestep. apply cf_appsubst. }
      eapply rt_trans.
      { eapply HINTcf_rator_step_compatibility.
        exact redx. }
      eapply HINTcf_rand_step_compatibility.
      exact redy. }
    apply normalize_refl.
    apply Tmcfσvalue_is_nf.
    apply Tmcfσvalue_app; apply Tmcfσnf_is_value; assumption.
  Qed.

  Lemma Tmcf_substvalue_normalize0' (x:Tmcf) (xV : Tmcfσvalue x) (nolam : nlamsInTmcfσValue x <= 0) {δ : Tmscf} (Hδ : Renaming δ)
    : normalize Tmcfσstep (Tmcf_subst x δ).
  Proof.
    revert nolam δ Hδ.
    induction xV; intros nolam σ Hσ.
    - apply normalizeσsubstπ₂Renaming.
      + exact H.
      + exact Hσ.
    - apply normalizeσsubstapp.
      + refine (IHxV1 _ _ Hσ).
        simpl in nolam. lia.
      + refine (IHxV2 _ _ Hσ).
        simpl in nolam. lia.
    - simpl in nolam.
      exfalso.
      inversion nolam.
  Qed.

  Lemma Tmcf_substvalue_normalizeS' (x:Tmcf) (xV : Tmcfσvalue x) (nλ : nat) (nlam : nlamsInTmcfσValue x <= nλ) {δ : Tmscf} (Hδ : Renaming δ)
    : normalize Tmcfσstep (Tmcf_subst x δ).
  Proof.
    revert x xV nlam δ Hδ.
    induction nλ; intros x xV nlam δ Hδ.
    { apply Tmcf_substvalue_normalize0'; assumption. }
    revert nlam δ Hδ.
    induction xV; intros nlam σ Hσ.
    - apply normalizeσsubstπ₂Renaming.
      + exact H.
      + exact Hσ.
    - apply normalizeσsubstapp.
      + refine (IHxV1 _ _ Hσ).
        simpl in nlam.
        lia.
      + refine (IHxV2 _ _ Hσ).
        simpl in nlam.
        lia.
    - apply normalizeσsubstlam.
      destruct (Renaming_lift Hσ) as [σ' [σred σUDC]].
      eapply normalizeσsubst_compatibility.
      { exact σred. }
      apply IHnλ.
      + exact xV.
      + assert (L: forall a b, S a <= S b -> a <= b).
        { lia. }
        apply L.
        exact nlam.
      + exact σUDC.
  Qed.

  Lemma Tmcf_substvalue_normalize'
  {x:Tmcf} (xV : Tmcfσvalue x)
  {δ : Tmscf} (Hδ : Renaming δ)
    : normalize Tmcfσstep (Tmcf_subst x δ).
  Proof.
    eapply Tmcf_substvalue_normalizeS'.
    - exact xV.
    - apply le_n.
    - exact Hδ.
  Qed.

End CountingLam.

Lemma normalizeσsubstid {x : Tmcf} (xN: normalize Tmcfσstep x)
  : normalize Tmcfσstep (Tmcf_subst x Tmscf_id).
Proof.
  destruct xN as [y [xred nfy ]].
  eapply normalize_trans.
  { eapply HINTsubst_Tmcf_step_compatibility.
    exact xred. }
  apply Tmcf_substvalue_normalize'.
  - apply Tmcfσnf_is_value. exact nfy.
  - repeat constructor.
Qed.

Lemma Tmcf_valuesubstvalue_normalize (x:Tmcf) (xV : Tmcfσvalue x) (δ : Tmscf) (δV : Tmscfσvalue δ)
  : normalize Tmcfσstep (Tmcf_subst x δ).
Proof.
  revert δ δV;
  induction xV as [ι Hι|x y xV IHxV yV IHyV|y yV IHy];
  intros δ δV.
  - induction δV.
    + destruct (cf_iter_π₁idP_to_cf_iter_π₁id Hι) as [i ?]; subst.
      destruct (cf_iter_π₁idP_to_cf_iter_π₁id H) as [j ?]; subst.
      split with (Tmcf_ref (i+j)); split.
      * apply Tmscf_substiterπids.
      * apply Tmcf_ref_nf.
    + eapply normalize_trans.
      { apply rt_step.
        apply cf_refl.
        apply cf_substπ₂. }
      destruct (cf_iter_π₁idP_to_cf_iter_π₁id Hι) as [i ?]; subst.
      destruct i as [|i].
      * split with y; split.
        --simpl.
          eapply rt_trans with (Tmcf_π₂ (Tmscf_snoc δ y)); auto 200 with AKcf sets.
        --apply Tmcfσvalue_is_nf. exact H.
      * eapply normalize_trans.
        { eapply HINTcf_π₂_step_compatibility.
          apply Tmscf_compiterπid. }
        apply cf_iter_π₂_normalization.
        apply Tmscfσvalue_snoc; assumption.
  - destruct (IHxV _ δV) as [x0 [redx nf_x]].
    destruct (IHyV _ δV) as [y0 [redy nf_y]].
    eapply normalize_trans.
    { eapply rt_trans.
      { onestep. apply cf_appsubst. }
      eapply rt_trans.
      { eapply HINTcf_rator_step_compatibility.
        exact redx. }
      eapply HINTcf_rand_step_compatibility.
      exact redy. }
    apply normalize_refl.
    apply Tmcfσvalue_is_nf.
    apply Tmcfσvalue_app; apply Tmcfσnf_is_value; assumption.
  - apply normalizeσsubstlam.
    unfold lift.
    assert (H : normalize Tmscfσstep
                  (Tmscf_snoc
                    (Tmscf_comp δ (Tmscf_π₁ Tmscf_id))
                    (Tmcf_π₂ Tmscf_id))).
      {
        - apply normalizeσsnoc.
          + split with (Tmcf_π₂ Tmscf_id); split.
          { auto with sets. }
          apply Tmcfσvalue_is_nf.
          apply Tmcfσvalue_π₂.
          apply cf_iter_π₁idP_id.
          + induction δV.
            * destruct (cf_iter_π₁idP_to_cf_iter_π₁id H) as [i ?]; subst.
              apply cf_comp_iterπ₁id_normalization.
              apply normalizeσTmscfvalue.
              apply Tmscfσvalue_iterπ₁id.
              apply cf_iter_π₁idP_π₁.
              apply cf_iter_π₁idP_id.
            * apply normalizeσsnocomp.
              ++apply IHδV.
              ++apply Tmcf_substvalue_normalize'.
                --exact H.
                --repeat constructor.
      }
      destruct H as [η [redη ηnf]].
      eapply normalize_trans with (Tmcf_subst y η).
      { fold Tmcfσconv.
        auto with AKcf sets. }
      apply IHy.
      apply Tmscfσnf_is_value.
      exact ηnf.
Qed.

Fixpoint Tmscf_normalization (δ:Tmscf)
  : normalize Tmscfσstep δ
with Tmscf_comprvalue_normalize (δ:Tmscf)
  : forall (σ:Tmscf) (σV : Tmscfσvalue σ), normalize Tmscfσstep (Tmscf_comp δ σ)
with Tmcf_normalization (x:Tmcf)
  : normalize Tmcfσstep x
with Tmcf_substvalue_normalize (x:Tmcf)
  : forall (σ:Tmscf) (σV :  normalize Tmscfσstep σ), normalize Tmcfσstep (Tmcf_subst x σ).
Proof.
  - induction δ.
    + destruct IHδ as [δ' [δred δnf]].
      destruct (Tmcf_normalization x) as [x' [xred xnf]].
      apply normalizeσsnoc.
      * apply (normalize_trans _ _ _ xred).
        apply normalize_refl.
        exact xnf.
      * apply (normalize_trans _ _ _ δred).
        apply normalize_refl.
        exact δnf.
    + split with (Tmscf_id); split.
      * auto with sets.
      * apply Tmscfσvalue_is_nf.
        apply Tmscfσvalue_iterπ₁id.
        apply cf_iter_π₁idP_id.
    + destruct IHδ2 as [δ2' [δ2red δ2nf]].
      eapply normalize_trans.
      { eapply HINTcf_compr_step_compatibility.
        exact δ2red. }
      apply Tmscf_comprvalue_normalize.
      apply Tmscfσnf_is_value.
      exact δ2nf.
    + destruct IHδ as [δ' [δred δnf]].
      eapply normalize_trans.
      { eapply HINTcf_π₁_step_compatibility.
        exact δred. }
      induction (Tmscfσnf_is_value _ δnf).
      * split with (Tmscf_π₁ δ0); split.
        --apply rt_refl.
        --apply Tmscfσvalue_is_nf.
          apply Tmscfσvalue_iterπ₁id.
          apply cf_iter_π₁idP_π₁.
          exact H.
      * split with δ0; split.
        --apply rt_step.
          apply cf_srefl.
          apply cf_π₁beta.
        --apply Tmscfσvalue_is_nf.
          exact t.
  - induction δ; intros σ σV.
    + eapply normalize_trans.
      { apply rt_step.
        apply cf_srefl.
        apply cf_snocomp. }
      destruct (Tmscf_comprvalue_normalize δ σ σV) as [η [redη ηnf]].
      destruct (Tmcf_substvalue_normalize x σ (normalizeσTmscfvalue σV)) as [z [redz znf]].
      apply normalizeσsnoc.
      * apply (normalize_trans _ _ _ redz).
        apply normalize_refl.
        exact znf.
      * apply (normalize_trans _ _ _ redη).
        apply normalize_refl.
        exact ηnf.
    + split with σ; split.
      * apply rt_step.
        apply cf_srefl.
        apply cf_idl.
      * apply Tmscfσvalue_is_nf.
        apply σV.
    + eapply normalize_trans.
      { apply rt_step.
        apply cf_srefl.
        apply cf_ass. }
      destruct (Tmscf_comprvalue_normalize δ2 σ σV) as [η [redη ηnf]].
      eapply normalize_trans with (Tmscf_comp δ1 η).
      {
        apply HINTcf_compr_step_compatibility.
        exact redη.
      }
      apply IHδ1.
      apply Tmscfσnf_is_value.
      exact ηnf.
    + eapply normalize_trans.
      { apply rt_step.
        apply cf_srefl.
        apply cf_π₁comp. }
      destruct (IHδ σ σV) as [η [redη ηnf]].
      eapply normalize_trans with (Tmscf_π₁ η).
      { apply HINTcf_π₁_step_compatibility.
        exact redη. }
      induction (Tmscfσnf_is_value _ ηnf).
      * split with (Tmscf_π₁ δ0); split.
        { apply rt_refl. }
        apply Tmscfσvalue_is_nf.
        apply Tmscfσvalue_iterπ₁id.
        apply cf_iter_π₁idP_π₁.
        exact H.
      * split with δ0; split.
        { apply rt_step.
        apply cf_srefl.
        apply cf_π₁beta. }
        apply Tmscfσvalue_is_nf.
        exact t.
  - induction x.
    + destruct (Tmscf_normalization δ) as [δ' [redδ δnf]].
      eapply normalize_trans with (Tmcf_subst x δ').
      { apply HINTsubst_Tmscf_step_compatibility.
        exact redδ. }
      apply (Tmcf_substvalue_normalize x).
      apply normalizeσTmscfvalue.
      apply Tmscfσnf_is_value.
      exact δnf.
    + destruct (Tmscf_normalization δ) as [δ' [redδ δnf]].
      eapply normalize_trans with (Tmcf_π₂ δ').
      { apply HINTcf_π₂_step_compatibility.
        exact redδ. }
      induction (Tmscfσnf_is_value _ δnf).
      * split with (Tmcf_π₂ δ0); split.
        { apply rt_refl. }
        apply Tmcfσvalue_is_nf.
        apply Tmcfσvalue_π₂.
        exact H.
      * split with y; split.
        { apply rt_step. apply cf_refl. apply cf_π₂beta. }
        apply Tmcfσvalue_is_nf.
        exact H.
    + apply normalizeσapp.
      * exact IHx1.
      * exact IHx2.
    + destruct IHx as [x' [xred xnf]].
      split with (Tmcf_lam x'); split.
      { apply HINTcf_lam_step_compatibility.
        apply xred. }
      apply Tmcfσvalue_is_nf.
      apply Tmcfσvalue_lam.
      apply Tmcfσnf_is_value.
      exact xnf.
  - induction x; intros σ σV.
    + eapply normalize_trans.
      { apply rt_step. apply cf_refl. apply cf_substsubst. }
      destruct σV as [σ' [σred σV]].
      destruct (Tmscf_comprvalue_normalize δ σ' (Tmscfσnf_is_value _ σV)) as [η [redη ηnf]].
      eapply normalize_trans with (Tmcf_subst x η).
      { apply HINTsubst_Tmscf_step_compatibility.
        eapply rt_trans with (Tmscf_comp δ σ'); autored. }
      apply IHx.
      apply normalize_refl.
      exact ηnf.
    + eapply normalize_trans.
      { apply rt_step.
        apply cf_refl.
        apply cf_substπ₂. }
      destruct σV as [σ' [σred σV]].
      destruct (Tmscf_comprvalue_normalize δ σ' (Tmscfσnf_is_value _ σV)) as [η [redη ηnf]].
      eapply normalize_trans with (Tmcf_π₂ η).
      { apply HINTcf_π₂_step_compatibility.
        eapply rt_trans with (Tmscf_comp δ σ'); autored. }
      induction (Tmscfσnf_is_value _ ηnf).
      * split with (Tmcf_π₂ δ0); split.
        { apply rt_refl. }
        apply Tmcfσvalue_is_nf.
        apply Tmcfσvalue_π₂.
        exact H.
      * split with y; split.
        { apply rt_step.
          apply cf_refl.
          apply cf_π₂beta. }
        apply Tmcfσvalue_is_nf.
        exact H.
    + apply normalizeσsubstapp.
      * apply (IHx1 _ σV).
      * apply (IHx2 _ σV).
    + destruct σV as [σ' [σred σV]].
      eapply normalize_trans with ((Tmcf_subst (Tmcf_lam x) σ')).
      { autored. }
      apply Tmscfσnf_is_value in σV.
      eapply normalize_trans.
      { apply rt_step.
        apply cf_refl.
        apply cf_lamsubst. }
      unfold lift.
      assert (H : normalize Tmscfσstep (Tmscf_comp σ' (Tmscf_π₁ Tmscf_id))).
      { clear σred.
        induction σV.
        - induction (cf_iter_π₁idP_to_cf_iter_π₁id H) as [i ?].
          subst.
          change (Tmscf_π₁ Tmscf_id) with (cf_iter_π₁ 1 Tmscf_id).
          eapply normalize_trans.
          { apply Tmscf_compiterπids. }
          split with (cf_iter_π₁ (i + 1) Tmscf_id); split.
          { apply rt_refl. }
          apply Tmscfσvalue_is_nf.
          apply Tmscfσvalue_iterπ₁id.
          apply Tmscfσvalue_cf_iter_π₁id.
        - eapply normalize_trans.
          { apply rt_step.
            apply cf_srefl.
            apply cf_snocomp. }

          destruct IHσV as [η [ηred ηnf]].
          eapply normalize_trans with (Tmscf_snoc η (Tmcf_subst y (Tmscf_π₁ Tmscf_id))).
          {
            apply HINTsnoc_Tmscf_step_compatibility.
            exact ηred.
          }
          destruct (Tmcf_valuesubstvalue_normalize y H (Tmscf_π₁ Tmscf_id)) as [z [redz znf]].
          { apply Tmscfσvalue_iterπ₁id. apply cf_iter_π₁idP_π₁. apply cf_iter_π₁idP_id. }
          apply normalizeσsnoc.
          * apply (normalize_trans _ _ _ redz).
            apply normalize_refl.
            exact znf.
          * apply normalize_refl.
            exact ηnf.
      }
      destruct H as [z [redz znf]].
      eapply normalize_trans.
      { eapply HINTcf_lam_step_compatibility.
        eapply HINTsubst_Tmscf_step_compatibility.
        eapply HINTsnoc_Tmscf_step_compatibility.
        apply redz. }
      destruct (Tmcf_substvalue_normalize x
        (Tmscf_snoc z (Tmcf_π₂ Tmscf_id)))
        as [u [redu unf]].
      { apply normalizeσsnoc.
        - apply normalizeσTmcfvalue.
          change (Tmcfσvalue (Tmcf_ref 0)).
          apply Tmcfσvalue_ref.
        - apply normalize_refl.
          exact znf. }
      split with (Tmcf_lam u); split.
      { apply HINTcf_lam_step_compatibility.
        apply redu. }
      apply Tmcfσvalue_is_nf.
      apply Tmcfσvalue_lam.
      apply Tmcfσnf_is_value.
      apply unf.
Defined.



Lemma nffun_Tmcf_ref {i} : nffun (Tmcf_normalization (Tmcf_ref i)) = Tmcf_ref i.
Proof.
  apply nffun_nf.
  apply Tmcf_ref_nf.
Qed.