From CwFdeBruijn.Syntax.dB Require Import dB occur.

Lemma slideS {f} : slide f ∘ S = S ∘ f.
Proof.
  reflexivity.
Qed.

Lemma liftS {δ} : (lift δ ∘ S) = (reindex S ∘ δ).
Proof.
  reflexivity.
Qed.

Lemma reindexisasubst f : reindex f = dB_subst (dB_ref ∘ f).
Proof.
  apply extensionality.
  intro x.
  revert f.
  induction x; intros f.
  + reflexivity.
  + simpl. f_equal. {apply IHx1. } {apply IHx2. }
  + simpl. f_equal. rewrite (IHx (slide f)). f_equal.
    apply extensionality. intro n. induction n.
    { reflexivity. } simpl.
    unfold compose. f_equal.
Qed.

Lemma dB_subst_reindex {δ f x} : dB_subst δ (reindex f x) = dB_subst (δ∘f) x.
Proof.
  revert δ f.
  induction x; intros δ f.
  + reflexivity.
  + simpl. f_equal. { apply IHx1. } {apply IHx2. }
  + simpl. f_equal. rewrite (IHx (lift δ) (slide f)).
    f_equal.
    apply extensionality.
    intro i; induction i; reflexivity.
Qed.

Lemma reindex_dB_subst {δ f x} : reindex f (dB_subst δ x) = dB_subst (reindex f ∘ δ) x.
Proof.
  revert δ f.
  induction x; intros δ f.
  + simpl. reflexivity.
  + simpl. f_equal. {apply IHx1. }{apply IHx2. }
  + simpl. f_equal.
    refine (eq_trans _ _).
    - apply IHx.
    - f_equal.
      apply extensionality.
      intro n. induction n.
      * reflexivity.
      * cbn. unfold compose.

      rewrite reindexisasubst.
      rewrite dB_subst_reindex.
      rewrite reindexisasubst.
      rewrite dB_subst_reindex.
      reflexivity.
Qed.

Definition lift_assign_comp (δ2: nat -> dB) (δ1 : nat -> dB)
  : assign_comp (lift δ2) (lift δ1) = lift (assign_comp δ2 δ1).
Proof.
  apply extensionality.
  intro n.

  revert δ2 δ1.

  induction n; intros δ2 δ1.
  + reflexivity.
  + cbn.
    rewrite dB_subst_reindex.
    unfold assign_comp.
    rewrite reindex_dB_subst.
    f_equal.
Qed.

Lemma dB_subst_subst {δ2 δ1} {x} : dB_subst δ2 (dB_subst δ1 x) = dB_subst (assign_comp δ1 δ2) x.
Proof.
  revert δ2 δ1.
  induction x; intros δ2 δ1.
  + unfold assign_comp.
    reflexivity.
  + simpl.
    f_equal. {apply IHx1. } {apply IHx2. }
  + simpl. f_equal.
    refine (eq_trans _ _).
    { apply IHx. }
    f_equal.
    apply lift_assign_comp.
Qed.

Lemma lift_dB_ref :lift dB_ref = dB_ref.
Proof.
  apply extensionality.
  intro n; induction n; reflexivity.
Qed.

Lemma dB_ref_Id x : dB_subst (dB_ref) x = x.
Proof.
  induction x; simpl.
  + reflexivity.
  + f_equal. {exact IHx1. } {exact IHx2. }
  + f_equal. rewrite lift_dB_ref. apply IHx.
Qed.

Lemma dB_ref_Id' : dB_subst dB_ref = id.
Proof.
  apply extensionality.
  apply dB_ref_Id.
Qed.

Lemma snoc_ref_slide_id {y} : (lift (dB_snoc dB_ref y) ∘ slide S) = dB_ref.
Proof.
  apply extensionality; intro n; induction n; reflexivity.
Qed.

Lemma snoc_ref_slide_id9 {y} : (lift (dB_snoc dB_ref y)) ∘ S = dB_snoc (dB_ref∘ S) (reindex S y).
Proof.
  apply extensionality. intro n. induction n.
  + simpl. reflexivity.
  + reflexivity.
Qed.

Lemma snoc_δ_S {x : dB} (δ : nat -> dB)
 : (dB_snoc δ x ∘ S) = δ.
Proof.
  apply extensionality.
  intro i.
  reflexivity.
Qed.

Lemma snoc_ref_S {x : dB}
 : (dB_snoc dB_ref x ∘ S) = dB_ref.
Proof.
  apply extensionality.
  reflexivity.
Qed.

Lemma subst_snoc_ref_reind_id {x y}: dB_subst (dB_snoc dB_ref y) (reindex S x) = x.
Proof.
  induction x.
  + reflexivity.
  + simpl. f_equal; assumption.
  + simpl.
    f_equal.
    rewrite dB_subst_reindex.
    rewrite snoc_ref_slide_id.
    apply dB_ref_Id.
Qed.

Lemma nocc_nsubst {x δ σ}
  (H : forall i, OccurP i x -> δ i = σ i)
  : dB_subst δ x = dB_subst σ x.
Proof.
  revert δ σ H.
  induction x; intros δ σ H.
  - simpl.
    apply H.
    constructor.
  - simpl.
    f_equal.
    + apply IHx1.
      intros i occ_ix1.
      apply H.
      apply OccurP_rator.
      exact occ_ix1.
    + apply IHx2.
      intros i occ_ix2.
      apply H.
      apply OccurP_rand.
      exact occ_ix2.
  - simpl.
    f_equal.
    apply IHx.
    intros i occ_ix.
    destruct i.
    { reflexivity. }
    simpl.
    f_equal.
    apply H.
    constructor.
    exact occ_ix.
Qed.

Lemma nocc_nsubst0 {x y} (H : ~ OccurP 0 x)
  : (dB_subst (reindex S ∘ dB_snoc dB_ref y) x) = x.
Proof.
  rewrite <-(dB_ref_Id x) at 2.
  apply nocc_nsubst.
  intros [|i] occ_ix.
  - exfalso. apply (H occ_ix).
  - reflexivity.
Qed.

Lemma ground_Reindex {x} (f:nat->nat)
  (H: forall i, not (OccurP i x))
  : reindex f x = x.
Proof.
  rewrite reindexisasubst.
  eapply eq_trans.
  { apply (nocc_nsubst (σ := dB_ref)).
    intros i occ.
    exfalso.
    apply (H _ occ). }
  apply dB_ref_Id.
Qed.