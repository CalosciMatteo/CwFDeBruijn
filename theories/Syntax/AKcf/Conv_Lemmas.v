From CwFdeBruijn.Syntax.AKcf Require Export AKcf_Conv GenRewr.

Open Scope AKcf.

Lemma cf_compπ₁id {δ : Tmscf} : (Tmscf_comp (Tmscf_π₁ (Tmscf_id)) δ) --s>* (Tmscf_π₁ δ).
Proof.
  eapply (rt_trans _ (Tmscfσstep) _ (Tmscf_π₁ (Tmscf_comp Tmscf_id δ)) ); fold Tmscfσconv; auto 6 with AKcf sets.
Qed.

Lemma cf_substref0 {δ : Tmscf} : (Tmcf_subst (Tmcf_π₂ Tmscf_id) δ) -->* (Tmcf_π₂ δ).
Proof.
  apply (rt_trans _ _ _ (Tmcf_π₂ (Tmscf_comp Tmscf_id δ))); auto with AKcf sets.
Qed.
#[export] Hint Resolve cf_substref0 : AKcf.

Lemma substref0π₁id (i:nat) : Tmcf_subst (Tmcf_π₂ Tmscf_id) (cf_iter_π₁ i Tmscf_id) -->* Tmcf_ref i.
Proof.
  induction i;
    apply (rt_trans _ _ _ _ _ (cf_substref0));
    auto with AKcf sets.
Qed.

Lemma cf_substrefsnoc {δ : Tmscf} {t : Tmcf} : Tmcf_subst (Tmcf_π₂ Tmscf_id) (Tmscf_snoc δ t) -->* t.
Proof.
  apply (rt_trans _ _ _ (Tmcf_π₂ (Tmscf_snoc δ t))); auto with AKcf sets.
  auto with AKcf sets.
  apply cf_substref0.
Qed.

Lemma Tmscf_compiterπ₁ (i : nat) (δ σ:Tmscf)
: Tmscf_comp (cf_iter_π₁ i δ) σ --s>* cf_iter_π₁ i (Tmscf_comp δ σ).
Proof.
  induction i.
  - simpl; auto with AKcf sets.
  - eapply rt_trans.
    { onestep; apply cf_π₁comp. }
    apply HINTcf_π₁_step_compatibility.
    exact IHi.
Qed.

Lemma Tmscf_compiterπid (i : nat) (δ:Tmscf)
: Tmscf_comp (cf_iter_π₁ i Tmscf_id) δ --s>* cf_iter_π₁ i δ.
Proof.
  induction i.
  - simpl; auto with AKcf sets.
  - simpl. simpl in IHi.
    apply (rt_trans _ _ _
      (Tmscf_π₁ (Tmscf_comp
        ((cf_iter_π₁ i Tmscf_id))
        (δ)))); fold Tmscfσconv; unfold cf_iter_π₁; simpl. auto with AKcf sets.
    apply HINTcf_π₁_step_compatibility.
    exact IHi.
Qed.

Lemma Tmscf_substref (δ : Tmscf) (i : nat)
  : Tmcf_subst (Tmcf_ref i) δ
  -->* cf_iter_π₂ i δ.
Proof.
  eapply rt_trans.
  { onestep.
    apply cf_substπ₂. }
  apply HINTcf_π₂_step_compatibility.
  apply Tmscf_compiterπid.
Qed.

Lemma Tmscf_compiterπids (i j : nat)
: Tmscf_comp (cf_iter_π₁ i Tmscf_id) (cf_iter_π₁ j Tmscf_id) --s>* cf_iter_π₁ (i + j) Tmscf_id.
Proof.
  induction i.
  - simpl. auto with AKcf sets.
  - simpl.
    eapply rt_trans.
    { onestep. apply cf_π₁comp. }
    apply HINTcf_π₁_step_compatibility.
    fold (iter Tmscf_π₁).
    apply IHi.
Qed.

Lemma Tmscf_nestediterπ₁ (i j : nat) (δ : Tmscf)
: (cf_iter_π₁ i (cf_iter_π₁ j δ)) = cf_iter_π₁ (i + j) δ.
Proof.
  induction i.
  - simpl. reflexivity.
  - unfold cf_iter_π₁. simpl. f_equal. apply IHi.
Qed.

Lemma cf_iter_π₁_snoc δ x i
  : cf_iter_π₁ (S i) (Tmscf_snoc δ x) --s> cf_iter_π₁ i δ.
Proof.
  rewrite cf_iter_π₁_flip.
  apply AKcfσstep_iter_π₁_compatibility.
  apply cf_srefl. apply cf_π₁beta.
Qed.

Lemma cf_iter_π₂_snoc δ x i
  : cf_iter_π₂ (S i) (Tmscf_snoc δ x) --> cf_iter_π₂ i δ.
Proof.
  unfold cf_iter_π₂.
  apply (cf_π₂_step_compatibility Tmcfσstep Tmscfσstep).
  { apply AKcfσstep_compatibility. }
  apply cf_iter_π₁_snoc.
Qed.

Lemma cf_substrefsnocid (i:nat)
: Tmcf_subst (Tmcf_ref (S i)) (Tmscf_snoc Tmscf_id (Tmcf_π₂ Tmscf_id)) -->* Tmcf_ref i.
Proof.
  eapply rt_trans.
  { apply rt_step. apply cf_refl. apply cf_substπ₂. }
  apply HINTcf_π₂_step_compatibility.
  eapply rt_trans.
  { apply Tmscf_compiterπid. }
  rewrite cf_iter_π₁_flip.
  apply AKcfσconv_iter_π₁_compatibility.
  auto with AKcf sets.
Qed.

Lemma cf_substrefsnocid' (i:nat)
: Tmcf_subst (Tmcf_ref i) (Tmscf_snoc Tmscf_id (Tmcf_π₂ Tmscf_id)) -->* Tmcf_ref (pred i).
Proof.
  destruct i.
  - apply cf_substrefsnoc.
  - apply cf_substrefsnocid.
Qed.

Lemma Tmscf_substiterπids (i j : nat): Tmcf_subst (cf_iter_π₂ i Tmscf_id) (cf_iter_π₁ j Tmscf_id) -->* cf_iter_π₂ (i + j) Tmscf_id.
Proof.
  induction i.
  - simpl. eauto with AKcf sets.
  - simpl.
    eapply rt_trans.
    { apply rt_step.
      apply cf_refl.
      apply cf_substπ₂. }
    eapply rt_trans.
    { eapply HINTcf_π₂_step_compatibility.
      apply Tmscf_compiterπids. }
    auto with AKcf sets.
Qed.

Lemma Tmcf_substliftref (i : nat): Tmcf_subst (Tmcf_ref i) (Tmscf_π₁ Tmscf_id) -->* Tmcf_ref (S i).
Proof.
  change (Tmscf_π₁ Tmscf_id) with (cf_iter_π₁ 1 Tmscf_id).
  assert (H : S i = i+1). {lia. }
  rewrite H.
  apply Tmscf_substiterπids.
Qed.

Lemma Tmcf_substliftsref (i j : nat): Tmcf_subst (Tmcf_ref i) (cf_iter_π₁ j Tmscf_id) -->* Tmcf_ref (i + j).
Proof.
  apply Tmscf_substiterπids.
Qed.

Lemma cf_substrefsnoc' i δ x
: Tmcf_subst (Tmcf_ref (S i)) (Tmscf_snoc δ x)
  -->* Tmcf_π₂ (cf_iter_π₁ i δ).
Proof.
  eapply rt_trans.
  { onestep.
    apply cf_substπ₂. }
  apply HINTcf_π₂_step_compatibility.
  eapply rt_trans.
  { apply Tmscf_compiterπid. }
  rewrite cf_iter_π₁_flip.
  apply AKcfσconv_iter_π₁_compatibility.
  onestep.
  apply cf_π₁beta.
Qed.

Lemma iter_lift_compatibility (δ σ: Tmscf) (H: δ --s>* σ) (i: nat)
: iter_lift i δ --s>* iter_lift i σ.
Proof.
  induction i.
  - exact H.
  - simpl. unfold iter_lift. simpl. unfold lift. auto with AKcf sets.
Qed.

Lemma lift_compatibility (δ σ: Tmscf) (H: δ --s>* σ)
: lift δ --s>* lift σ.
Proof.
  apply (iter_lift_compatibility _ _ H 1).
Qed.

Definition iter_lift_flip i δ
: iter_lift (S i) δ = (iter_lift i (lift δ))
:= iter_flip lift i δ.

Lemma cf_iter_π₁_split {i} δ {j} d (H : i = d + j)
: cf_iter_π₁ i δ = (cf_iter_π₁ j (cf_iter_π₁ d δ)).
Proof.
  revert δ i j H.
  induction d; intros δ i j H.
  + f_equal.
    exact H.
  + subst.
    assert (H' : S d +j  = S (d+j)). { lia. }
    rewrite H'.
    rewrite !cf_iter_π₁_flip.
    apply IHd.
    reflexivity.
Qed.

Lemma iter_lift_split {i} δ {j} d (H : i = d + j)
: iter_lift i δ = (iter_lift j (iter_lift d δ)).
Proof.
  revert δ i j H.
  induction d; intros δ i j H.
  + simpl in H.
    destruct H.
    reflexivity.
  + subst.
    assert (H' : S d + j  = S (d+j)). { lia. }
    rewrite H'.
    rewrite !iter_lift_flip.
    apply IHd.
    reflexivity.
Qed.

Lemma cf_iter_π₁_lift_eq (i : nat) (δ : Tmscf)
  : cf_iter_π₁ i (iter_lift (S i) δ)
    --s>* Tmscf_snoc (Tmscf_comp δ (cf_iter_π₁ (S i) Tmscf_id)) (Tmcf_ref i).
Proof.
  revert δ.
  induction i; intro δ.
  - auto with AKcf sets.
  - rewrite (iter_lift_flip (S i) δ).
    cbn - [iter_lift].
    eapply rt_trans.
    {
      eapply HINTcf_π₁_step_compatibility.
      exact (IHi (lift δ)).
    }
    eapply rt_trans.
    {
      onestep.
      apply cf_π₁beta.
    }
    eapply rt_trans.
    {
      onestep.
      apply cf_snocomp.
    }
    eapply rt_trans with (Tmscf_snoc (Tmscf_comp (Tmscf_comp δ (Tmscf_π₁ Tmscf_id)) (cf_iter_π₁ (S i) Tmscf_id))(Tmcf_ref (S i))).
    { fold Tmscfσconv. eauto with AKcf sets. }
    fold Tmscfσconv.
    apply HINTsnoc_Tmscf_step_compatibility.
    eapply rt_trans.
    {
      onestep.
      apply cf_ass.
    }
    apply HINTcf_compr_step_compatibility.
    eapply rt_trans.
    {
      apply (Tmscf_compiterπids 1 (S i)).
    }
    apply rt_refl.
Qed.

Lemma cf_iter_π₂_lift (i j : nat) (H:i < j) (δ : Tmscf) : (cf_iter_π₂ i (iter_lift j δ)) -->* (Tmcf_ref i).
Proof.
  assert (E : j = j-(S i)+(S i)). {lia. }
  rewrite (iter_lift_split δ (j-(S i)) E).
  eapply rt_trans.
  {
    eapply HINTcf_π₂_step_compatibility.
    apply (cf_iter_π₁_lift_eq i ((iter_lift (j - S i) δ))).
  }
  apply rt_step.
  apply cf_refl.
  apply cf_π₂beta.
Qed.

Lemma cf_iter_π₁_lift_eq' (i : nat) (δ : Tmscf)
  : cf_iter_π₁ (S i) (iter_lift (S i) δ) --s>* (Tmscf_comp δ (cf_iter_π₁ (S i) Tmscf_id)).
Proof.
  eapply rt_trans.
  { simpl. eapply HINTcf_π₁_step_compatibility. apply cf_iter_π₁_lift_eq. }
  onestep.
  apply cf_π₁beta.
Qed.

Lemma cf_iter_π₁_more_lift (i j: nat) (H: S j < i) (δ : Tmscf)
  : cf_iter_π₁ i (iter_lift (S j) δ) --s>* cf_iter_π₁ (i-(S j)) (Tmscf_comp δ (cf_iter_π₁ (S j) Tmscf_id)).
Proof.
  assert (E : i = j + (i-j)). { lia. }
  rewrite (cf_iter_π₁_split (iter_lift (S j) δ) j E).
  eapply rt_trans.
  { apply AKcfσconv_iter_π₁_compatibility.
    apply cf_iter_π₁_lift_eq. }
  assert (L : i - j  = S (i - S j)). { lia. }
  rewrite L.
  eapply rt_trans.
  { rewrite cf_iter_π₁_flip.
    apply AKcfσconv_iter_π₁_compatibility.
    apply rt_step.
    apply cf_srefl.
    apply cf_π₁beta. }
  apply rt_refl.
Qed.

Lemma cf_iter_π₂_lift_id {i j} (H : i <= j)
: (cf_iter_π₂ i (iter_lift j Tmscf_id)) -->* (Tmcf_ref i).
Proof.
  destruct (le_lt_eq_dec i j H) as [lt|eq].
  - apply cf_iter_π₂_lift.
    exact lt.
  - subst.
    destruct j.
    + apply rt_refl.
    + eapply HINTcf_π₂_step_compatibility.
      eapply rt_trans.
      { apply cf_iter_π₁_lift_eq'. }
      onestep. apply cf_idl.
Qed.

Lemma cf_iter_π₁_more_lift_id {i j} (H: j < i)
  : cf_iter_π₁ i (iter_lift j Tmscf_id) --s>* cf_iter_π₁ i Tmscf_id.
Proof.
  destruct j.
  { apply rt_refl. }
  eapply rt_trans. { apply cf_iter_π₁_more_lift. exact H. }
  eapply rt_trans. { apply AKcfσconv_iter_π₁_compatibility. onestep. apply cf_idl. }
  rewrite Tmscf_nestediterπ₁.
  assert (e:(i - S j + S j = i)). { lia. } rewrite e. apply rt_refl.
Qed.

Section InversionOfApp.

Local Definition isApp := fun a => match a with
| b @ c => True
| _ => False
end.

Lemma Tmcfσstep_of_app {a b y} (H : a @ b --> y)
  : isApp y.
Proof.
  inversion H.
  1: inversion H0.
  all: now cbn.
Qed.

Lemma Tmcfσconv_of_app {a b y} (H : a @ b -->* y)
  : isApp y.
Proof.
  generalize (I : isApp (a @ b)).
  induction H.
  - intro.
    destruct x; try inversion H0.
    apply (Tmcfσstep_of_app H).
  - now idtac.
  - intro is; exact (IHclos_refl_trans2 (IHclos_refl_trans1 is)).
Qed.


Lemma Tmcfσstep_to_rator {a' b' a b} (H: a' @ b' --> a @ b)
  : a' -->* a.
Proof.
  inversion H; subst.
  - inversion H0.
  - now rewrite H1.
  - reflexivity.
Qed.
Lemma Tmcfσstep_to_rand {a' b' a b} (H: a' @ b' --> a @ b)
  : b' -->* b.
Proof.
  inversion H; subst.
  - inversion H0.
  - reflexivity.
  - now rewrite H1.
Qed.

Local Definition getRator := fun a => match a with
| b @ c => b
| _ => Tmcf_ref 0
end.
Local Definition getRand := fun a => match a with
| b @ c => c
| _ => Tmcf_ref 0
end.


Lemma Tmcfσconv_to_rator {a' b' a b} (H: a' @ b' -->* a @ b)
  : a' -->* a.
Proof.
  change (getRator (a' @ b') -->* getRator (a @ b)).
  assert (H1n := (clos_rt_rt1n _ _ _ _ H)).
  clear H.
  generalize (I : isApp (a' @ b')).
  generalize (I : isApp (a @ b)).
  
  induction H1n.
  - reflexivity.
  - destruct z, x; intros isApp1 isApp2;
     try (inversion isApp1); try (inversion isApp2).
    clear isApp1 isApp2.
    specialize (IHH1n I).
    inversion H; subst; try solve_by_invert.
    + cbn; etransitivity; [now rewrite H3|apply (IHH1n I)].
    + apply (IHH1n I).
Qed.
Lemma Tmcfσconv_to_rand {a' b' a b} (H: a' @ b' -->* a @ b)
  : b' -->* b.
Proof.
  change (getRand (a' @ b') -->* getRand (a @ b)).
  assert (H1n := (clos_rt_rt1n _ _ _ _ H)).
  clear H.
  generalize (I : isApp (a' @ b')).
  generalize (I : isApp (a @ b)).
  
  induction H1n.
  - reflexivity.
  - destruct z, x; intros isApp1 isApp2;
     try (inversion isApp1); try (inversion isApp2).
    clear isApp1 isApp2.
    specialize (IHH1n I).
    inversion H; subst; try solve_by_invert.
    + apply (IHH1n I).
    + cbn; etransitivity; [now rewrite H3|apply (IHH1n I)].
Qed.

End InversionOfApp.