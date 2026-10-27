From CwFdeBruijn.Syntax.AKcf Require Export AKcf context context_Conv context_minimal.
From CwFdeBruijn.Syntax.AKcf Require Import AKcf_Conv substid GenRewr finitary.
Require Import Setoid Morphisms RelationClasses.
From CwFdeBruijn.Syntax.AK Require Export AK AK_Conv.

Fixpoint Tmcf_of_Tm {p} (x:Tm p) : Tmcf :=
match x with
  | Tm_subst x δ =>
      Tmcf_subst (Tmcf_of_Tm x) (Tmscf_of_Tms δ)
  | Tm_π₂ δ => Tmcf_π₂ (Tmscf_of_Tms δ)
  | Tm_app x y => Tmcf_app (Tmcf_of_Tm x) (Tmcf_of_Tm y)
  | Tm_lam x => Tmcf_lam (Tmcf_of_Tm x)
end
with Tmscf_of_Tms {p q} (δ:Tms p q) : Tmscf :=
match δ with
  | Tms_nil p => cf_iter_π₁ p (Tmscf_id)
  | Tms_snoc δ x => Tmscf_snoc (Tmscf_of_Tms δ) (Tmcf_of_Tm x)
  | Tms_id p => Tmscf_id
  | Tms_comp δ₁ δ₂ => Tmscf_comp (Tmscf_of_Tms δ₁) (Tmscf_of_Tms δ₂)
  | Tms_π₁ δ => Tmscf_π₁ (Tmscf_of_Tms δ)
end.

Fixpoint contextFromTm {p} (x:Tm p) {struct x}
  : cfcontext p (Tmcf_of_Tm x)
with assignFromTms {p q : nat} (δ : Tms p q) {struct δ}
  : cfassign p q (Tmscf_of_Tms δ).
Proof.
{ induction x as [q x IH p δ| δ | p x IHx | p x IH].
  + simpl.
    refine (cfcontext_subst _ _).
    - exact IH.
    - apply assignFromTms.
  + simpl.
    refine (cfcontext_π₂ _).
    apply assignFromTms.
  + simpl.
    refine (cfcontext_app _ _); assumption.
  + simpl.
    refine (cfcontext_lam _).
    exact IH.
}
{ induction δ as [p0|p0 q0 δ IHδ x'| |p0 q0 δ₁ IHδ₁ r0 δ₂ IHδ₂|p0 q0 δ IHδ].
  + apply cfassign_iter_π₁.
    rewrite Nat.add_0_r.
    apply cfassign_id.
  + simpl.
    refine (cfassign_snoc _ _).
    - exact IHδ.
    - apply contextFromTm.
  + simpl.
    apply cfassign_id.
  + simpl.
    refine (cfassign_comp _ _).
    - exact IHδ₁.
    - exact IHδ₂.
  + simpl.
    refine (cfassign_π₁ _).
    exact IHδ.
}
Defined.

Fixpoint Tmscf_of_Tms_proper {p q} : Proper ((@Tmsσstep p q) ==> Tmscfσeq) Tmscf_of_Tms
with Tmcf_of_Tm_proper {p} : Proper ((@Tmσstep p) ==> Tmcfσeq) Tmcf_of_Tm.
Proof.
{ intros a b red.
  induction red.
    all: try (simpl; now rewrite IHred).
    2: simpl; now rewrite H.
  induction H.
  all: try (simpl; autored).
  apply cfassignm0, assignFromTms.
} 
{ intros δ γ red.
  induction red.
    all: try (simpl; now rewrite IHred).
    2,3: simpl; now rewrite H.
  induction H.
  all: try (simpl; autored).
  apply subst_id.
}
Qed.

Fixpoint Tm_of_Tmcf (x:Tmcf) {p:nat}
  (Hx:cfcontext p x) {struct x}
  : Tm p
with Tms_of_Tmscf (δ : Tmscf) {p0 q0 : nat}
  (Hδ: cfassign p0 q0 δ) {struct δ} : Tms p0 q0.
Proof.
{ induction x.
  - refine (Tm_subst _ _ ).
    + apply (Tm_of_Tmcf x).
      apply (contextof_subst Hx).
    + apply (Tms_of_Tmscf δ).
      exact (assignof_subst Hx).
  - refine (Tm_π₂ _).
    apply (Tms_of_Tmscf δ).
    exact (assignof_π₂ Hx).
  - refine (Tm_app _ _).
    + apply (Tm_of_Tmcf _ _ (contextof_rator Hx)).
    + apply (Tm_of_Tmcf _ _ (contextof_rand Hx)).
  - apply Tm_lam.
    apply (Tm_of_Tmcf x).
    exact (contextof_lam Hx).
}
{ induction δ.
  - destruct q0.
    { exfalso. exact (contextof_snoc_false Hδ). }
    apply Tms_snoc.
    + apply (Tms_of_Tmscf δ).
      exact (assignof_snoc Hδ).
    + apply (Tm_of_Tmcf x).
      exact (contextof_snoc Hδ).
  - destruct (contextof_id Hδ).
    apply Tms_id.
  - eapply (Tms_comp).
    + apply (Tms_of_Tmscf δ1).
      exact (assignlof_comp Hδ).
    + apply (Tms_of_Tmscf δ2).
      exact (assignrof_comp Hδ).
  - apply Tms_π₁.
    apply (Tms_of_Tmscf δ).
    exact (assignof_π₁ Hδ).
}
Defined.

Open Scope AK.

Section AKcf_to_AK_Compatibility.

Fixpoint cfcontext_irrelevance_Tm_of_Tmcf {p :nat} {x :Tmcf}
  (ctx1 : cfcontext p x) (ctx2 : cfcontext p x) {struct x}
  : Tm_of_Tmcf x ctx1 = Tm_of_Tmcf x ctx2
with cfassign_irrelevance_Tms_of_Tmscf {p q :nat} {δ :Tmscf}
  (ass1 : cfassign p q δ) (ass2 : cfassign p q δ) {struct δ}
  : Tms_of_Tmscf δ ass1 = Tms_of_Tmscf δ ass2.
Proof.
{ destruct x.
  - simpl.
    refine (f_equal2 (fun x => fun δ => Tm_subst x δ) _ _).
    + apply (cfcontext_irrelevance_Tm_of_Tmcf _ x).
    + apply (cfassign_irrelevance_Tms_of_Tmscf _ _ δ).
  - simpl.
    f_equal.
    apply (cfassign_irrelevance_Tms_of_Tmscf _ _ δ).
  - simpl.
    refine (f_equal2 (fun x => fun y => Tm_app x y) _ _).
    + apply (cfcontext_irrelevance_Tm_of_Tmcf _ x1).
    + apply (cfcontext_irrelevance_Tm_of_Tmcf _ x2).
  - simpl.
    f_equal.
    apply (cfcontext_irrelevance_Tm_of_Tmcf _ x).
}
{ destruct δ.
  - destruct q.
    { exfalso. inversion ass1. }
    simpl.
    refine (f_equal2 (fun δ => fun x => Tms_snoc δ x) _ _).
    + apply (cfassign_irrelevance_Tms_of_Tmscf _ _ δ).
    + apply (cfcontext_irrelevance_Tm_of_Tmcf _ x).
  - f_equal.
    apply proof_irrelevance.
  - simpl.
    refine (f_equal2 (fun δ1 => fun δ2 => Tms_comp δ1 δ2) _ _).
    + apply (cfassign_irrelevance_Tms_of_Tmscf _ _ δ1).
    + apply (cfassign_irrelevance_Tms_of_Tmscf _ _ δ2).
  - simpl.
    f_equal.
    apply (cfassign_irrelevance_Tms_of_Tmscf _ _ δ).
}
Qed.

(* eqtc stand for equation through casting *)
(* ctc stand for conversion through casting *)
Lemma Tm_of_Tmcf_eqtc_substsubst {p q q' r r'}
  {x : Tmcf}
  {δ σ : Tmscf}
  {ctx_x : cfcontext q x}
  {ctx_x' : cfcontext q' x}
  {ass_δ : cfassign r q δ}
  {ass_δ' : cfassign r' q' δ}
  {ass_σ : cfassign p r σ}
  {ass_σ' : cfassign p r' σ}
  (E_q: q' = q)
  (E_r: r' = r)
  :
  Tm_subst
    (Tm_of_Tmcf x ctx_x)
    (Tms_comp
      (Tms_of_Tmscf δ ass_δ)
      (Tms_of_Tmscf σ ass_σ)) =
  Tm_subst
    (Tm_of_Tmcf x ctx_x')
    (Tms_comp
      (Tms_of_Tmscf δ ass_δ')
      (Tms_of_Tmscf σ ass_σ')).
Proof.
  destruct E_q.
  destruct E_r.
  refine (f_equal2 (fun x => fun δ => Tm_subst x δ) _ _).
  - apply cfcontext_irrelevance_Tm_of_Tmcf.
  - refine (f_equal2 (fun δ1 => fun δ2 =>Tms_comp δ1 δ2) _ _).
    + apply cfassign_irrelevance_Tms_of_Tmscf.
    + apply cfassign_irrelevance_Tms_of_Tmscf.
Qed.

Lemma Tm_of_Tmcf_eqtc_lamsubst1 {p q q'}
  {x : Tmcf}
  {δ : Tmscf}
  {ctx_x : cfcontext q x}
  {ctx_x' : cfcontext q' x}
  {ass_dδ : cfassign p q (lift δ)}
  {ass_dδ' : cfassign p q' (lift δ)}
  (E_q: q' = q)
  :
  Tm_subst
    (Tm_of_Tmcf x ctx_x)
    (Tms_of_Tmscf (lift δ) ass_dδ) =
  Tm_subst
    (Tm_of_Tmcf x ctx_x')
    (Tms_of_Tmscf (lift δ) ass_dδ').
Proof.
  destruct E_q.
  f_equal.
  - apply cfcontext_irrelevance_Tm_of_Tmcf.
  - apply cfassign_irrelevance_Tms_of_Tmscf.
Qed.

Lemma Tm_of_Tmcf_eqtc_lamsubst0 {p p' q}
  {δ : Tmscf}
  {ass_δ : cfassign p q δ}
  {ass_δ' : cfassign p' q δ}
  {ass_id : cfassign (S p') (S p) Tmscf_id}
  {ass_id' : cfassign (S p') (S p') Tmscf_id}
  (E : p' = p)
  : Tms_comp
      (Tms_of_Tmscf δ ass_δ)
      (Tms_π₁ (Tms_of_Tmscf Tmscf_id ass_id)) =
    Tms_comp
      (Tms_of_Tmscf δ ass_δ')
      (Tms_π₁ (Tms_of_Tmscf Tmscf_id ass_id')).
Proof.
  destruct E.
  f_equal.
  - apply cfassign_irrelevance_Tms_of_Tmscf.
  - f_equal.
    apply cfassign_irrelevance_Tms_of_Tmscf.
Defined.

Lemma Tm_of_Tmcf_eqtc_substπ₂ {p q q' r r'}
  {δ σ: Tmscf}
  {ass_δ : cfassign r (S q) δ}
  {ass_δ': cfassign r' (S q') δ}
  {ass_σ : cfassign p r σ}
  {ass_σ' : cfassign p r' σ}
  (E_q : q' = q)
  (E_r : r' = r)
  : Tm_π₂ (Tms_comp
      (Tms_of_Tmscf δ ass_δ)
      (Tms_of_Tmscf σ ass_σ)) =
    Tm_π₂ (Tms_comp
      (Tms_of_Tmscf δ ass_δ')
      (Tms_of_Tmscf σ ass_σ')).
Proof.
  destruct E_q. destruct E_r.
  f_equal.
  f_equal.
  - apply cfassign_irrelevance_Tms_of_Tmscf.
  - apply cfassign_irrelevance_Tms_of_Tmscf.
Defined.

Lemma Tm_of_Tmcf_ctc_lamsubst {q p}
  {δ : Tmscf}
  (ass_id1 : cfassign (S p) (S p) Tmscf_id)
  (ass_id2 : cfassign (S p) (S p) Tmscf_id)
  {ass_δ : cfassign p q δ}
  {ass_δ' : cfassign p q δ}
  :
    (Tms_snoc
      (Tms_comp (Tms_of_Tmscf δ ass_δ) (Tms_π₁ (Tms_id (S p))))
      (Tm_π₂ (Tms_id (S p)))) =
    (Tms_snoc
      (Tms_comp (Tms_of_Tmscf δ ass_δ') (Tms_π₁ (Tms_of_Tmscf Tmscf_id ass_id1)))
      (Tm_π₂ (Tms_of_Tmscf Tmscf_id ass_id2))).
Proof.
  f_equal.
  - f_equal.
    + apply cfassign_irrelevance_Tms_of_Tmscf.
    + f_equal.
      eapply eq_trans with (Tms_of_Tmscf Tmscf_id (cfassign_id (S p))).
      * reflexivity.
      * apply cfassign_irrelevance_Tms_of_Tmscf.
  - f_equal.
    eapply eq_trans with (Tms_of_Tmscf Tmscf_id (cfassign_id (S p))).
    + reflexivity.
    + apply cfassign_irrelevance_Tms_of_Tmscf.
Qed.

Lemma Tms_of_Tmscf_ctc_comp {q r r' p}
  {δ σ: Tmscf}
  {ass_δ : cfassign r q δ}
  {ass_δ' : cfassign r' q δ}
  {ass_σ : cfassign p r σ}
  {ass_σ' : cfassign p r' σ}
  (E: r' = r)
  : Tms_comp
      (Tms_of_Tmscf δ ass_δ)
      (Tms_of_Tmscf σ ass_σ)
  = (Tms_comp
      (Tms_of_Tmscf δ ass_δ')
      (Tms_of_Tmscf σ ass_σ')).
Proof.
  destruct E.
  f_equal; apply cfassign_irrelevance_Tms_of_Tmscf.
Defined.

Lemma Tms_of_Tmscf_ctc_subst {p q q'}
  {δ δ': Tmscf}
  {x x': Tmcf}
  {ass_δ : cfassign p q δ}
  {ass_δ' : cfassign p q' δ'}
  {ctx_x : cfcontext q x}
  {ctx_x' : cfcontext q' x'}
  (E: q' = q)
  (x_conv :
    (Tm_of_Tmcf x ctx_x) <-->*
    eq_rect q' Tm (Tm_of_Tmcf x' ctx_x') q E)
  (δ_conv : (Tms_of_Tmscf δ ass_δ) <--s>*
    eq_rect q' (Tms p) (Tms_of_Tmscf δ' ass_δ') q E)
  : Tm_subst
      (Tm_of_Tmcf x ctx_x)
      (Tms_of_Tmscf δ ass_δ)
  <-->* Tm_subst
      (Tm_of_Tmcf x' ctx_x')
      (Tms_of_Tmscf δ' ass_δ').
Proof.
  destruct E.
  simpl in *.
  eapply rst_trans.
  { eapply HINTsubst_Tm_step_compatibility.
    exact x_conv. }
  eapply HINTsubst_Tms_step_compatibility.
  exact δ_conv.
Qed.

Lemma Tms_of_Tmscf_ctc_π₂ {p q q'}
  {δ δ': Tmscf}
  (ass_δ : cfassign p (S q) δ)
  (ass_δ' : cfassign p (S q') δ')
  (E: q' = q)
  (δ_conv : (Tms_of_Tmscf δ ass_δ) <--s>*
    eq_rect q' (fun q => Tms p (S q)) (Tms_of_Tmscf δ' ass_δ') q E)
  : Tm_π₂ (Tms_of_Tmscf δ (ass_δ))
  <-->* Tm_π₂ (Tms_of_Tmscf δ' (ass_δ')).
Proof.
  destruct E.
  simpl in *.
  eapply HINT_π₂_step_compatibility.
  exact δ_conv.
Qed.

Lemma Tms_of_Tmscf_ctc_ass {p q q' r r' s}
  {δ σ ν: Tmscf}
  (ass_δ : cfassign r s δ)
  {ass_δ' : cfassign r' s δ}
  (ass_σ : cfassign q r σ)
  {ass_σ' : cfassign q' r' σ}
  (ass_ν : cfassign p q ν)
  {ass_ν' : cfassign p q' ν}
  (E_q: q' = q)
  (E_r: r' = r)
  : Tms_comp (Tms_of_Tmscf δ ass_δ)
      (Tms_comp
        (Tms_of_Tmscf σ ass_σ)
        (Tms_of_Tmscf ν ass_ν))
  = Tms_comp (Tms_of_Tmscf δ ass_δ')
      (Tms_comp
        (Tms_of_Tmscf σ ass_σ')
        (Tms_of_Tmscf ν ass_ν')).
Proof.
  destruct E_r.
  f_equal.
  { apply cfassign_irrelevance_Tms_of_Tmscf. }
  apply Tms_of_Tmscf_ctc_comp.
  exact E_q.
Defined.

Lemma Tms_of_Tmscf_ctc_snocomp {q r r' r'' p}
  {δ σ : Tmscf} {t : Tmcf}
  {ass_δ : cfassign r q δ}
  {ass_δ' : cfassign r' q δ}
  {ass_σ : cfassign p r σ}
  {ass_σ' : cfassign p r' σ}
  {ass_σ'' : cfassign p r'' σ}
  {ctx_t : cfcontext r'' t}
  {ctx_t' : cfcontext r' t}
  (E : r = r')
  (E' : r' = r'')
  : Tms_snoc
      (Tms_comp (Tms_of_Tmscf δ ass_δ) (Tms_of_Tmscf σ ass_σ))
      (Tm_subst (Tm_of_Tmcf t ctx_t) (Tms_of_Tmscf σ ass_σ''))
  = Tms_snoc
      (Tms_comp (Tms_of_Tmscf δ ass_δ') (Tms_of_Tmscf σ ass_σ'))
      (Tm_subst (Tm_of_Tmcf t ctx_t') (Tms_of_Tmscf σ ass_σ')).
Proof.
  destruct E.
  destruct E'.
  f_equal.
  - apply Tms_of_Tmscf_ctc_comp.
    reflexivity.
  - f_equal.
    + apply cfcontext_irrelevance_Tm_of_Tmcf.
    + apply cfassign_irrelevance_Tms_of_Tmscf.
Qed.

Lemma Tms_of_Tmscf_ctc_πeta {q q' p}
  {δ : Tmscf}
  {ass_δ ass_δ' : cfassign p (S q) δ}
  {ass_δ'' : cfassign p (S q') δ}
  (E : q = q')
  : (Tms_snoc
      (Tms_π₁ (Tms_of_Tmscf δ ass_δ'))
      (Tm_π₂ (Tms_of_Tmscf δ ass_δ'')))
  = (Tms_snoc
      (Tms_π₁ (Tms_of_Tmscf δ ass_δ))
      (Tm_π₂ (Tms_of_Tmscf δ ass_δ))).
Proof.
  destruct E.
  f_equal.
  - f_equal.
    apply cfassign_irrelevance_Tms_of_Tmscf.
  - f_equal.
    apply cfassign_irrelevance_Tms_of_Tmscf.
Qed.


Lemma cfassign_lift {p q} {δ : Tmscf} (ass : cfassign p q δ)
  : cfassign (S p) (S q) (lift δ).
  Proof.
    unfold lift.
    apply cfassign_snoc.
    - eapply cfassign_comp.
      + exact ass.
      + apply cfassign_π₁.
        apply cfassign_id.
    - eapply cfcontext_π₂.
      apply cfassign_id.
  Defined.

Lemma Tm_of_Tmcf_compatibility'' {px py:nat} {x y : Tmcf}
  (ctx_x : cfcontext px x) (ctx_y : cfcontext py y)
  (E : py = px)
  (red : Tmcfσstep' x y)
  : (Tm_of_Tmcf x ctx_x) <-->* eq_rect py Tm (Tm_of_Tmcf y ctx_y) _ E.
Proof.
  revert px py ctx_x ctx_y E.
  induction red; intros px py ctx_x ctx_y ; destruct E.
  - simpl.
    eapply rst_trans.
    { onestepf. apply substsubst. }
    apply rst_refl_propositional.
    apply Tm_of_Tmcf_eqtc_substsubst.
    + rewrite Minass_p_comp_beta, Minass_q_comp_beta.
      lia.
    + rewrite Minass_p_comp_beta, Minass_q_comp_beta.
      inversion ctx_x; subst.
      inversion Hx; subst.
      destruct (Minass_minimal _ _ _ Hδ) as [i [? ?]].
      destruct (Minass_minimal _ _ _ Hδ0) as [j [? ?]].
      specialize (Minctx_minimal _ _ Hx0).
      unfold Minass_p, Minass_q.
      lia.
  - simpl.
    eapply rst_trans.
    { onestepf. apply π₂beta. }
    apply rst_refl_propositional.
    apply cfcontext_irrelevance_Tm_of_Tmcf.
  - cbn [eq_rect].
    eapply rst_trans.
    { simpl. onestepf. apply lamsubst. }
    apply rst_refl_propositional.
    cbn -[lift].
    f_equal.

    generalize (contextof_subst ctx_x);
      generalize (assignof_subst ctx_x);
      clear ctx_x; intros ass_δ ctx_lx.
    generalize (contextof_lam ctx_lx); clear ctx_lx; intros ctx_t.
    generalize  (contextof_lam ctx_y); clear ctx_y; intros ctx_tdδ.
    generalize (assignof_subst ctx_tdδ);
      generalize (contextof_subst ctx_tdδ);
      clear ctx_tdδ;
      intros ctx_t' ass_dδ.
    assert (Tms_of_Tmscf Tmscf_id (cfassign_id (S py)) = Tms_id (S py)).
    { reflexivity. }
    destruct H.
    assert (H:
      Tms_of_Tmscf (lift δ) (cfassign_lift ass_δ) =
      Tms_snoc
        (Tms_comp
          (Tms_of_Tmscf δ ass_δ)
          (Tms_π₁ (Tms_of_Tmscf Tmscf_id (cfassign_id (S py)))))
        (Tm_π₂ (Tms_of_Tmscf Tmscf_id (cfassign_id (S py))))
    ).
    { unfold lift.
      cbn - [Tms_of_Tmscf].
      refine (eq_trans
        (y:= (Tms_snoc
          (Tms_comp
            (Tms_of_Tmscf δ _)
            (Tms_π₁ (Tms_of_Tmscf Tmscf_id _)))
          (Tm_π₂ (Tms_of_Tmscf Tmscf_id _))))
        _ _).
        { reflexivity. }
      f_equal.
      - apply Tm_of_Tmcf_eqtc_lamsubst0.
        destruct (Minass_minimal _ _ _ ass_δ) as [i [? ?]].
        unfold Minass_p, Minass_q. lia.
      - f_equal.
        apply cfassign_irrelevance_Tms_of_Tmscf. }
    destruct H.
    apply Tm_of_Tmcf_eqtc_lamsubst1.
    unfold lift.
    Minbeta.
    cbn.
    lia.
  - simpl.
    eapply rst_trans.
    { apply substπ₂. }
    apply rst_refl_propositional.
    apply Tm_of_Tmcf_eqtc_substπ₂.
    + Minbeta.
      lia.
    + Minbeta.
      assert (P : Minass_q σ = 0 \/ S (pred (Minass_q σ)) = (Minass_q σ)). {lia. }
      destruct P.
      * rewrite H.
        inversion ctx_x; subst.
        inversion Hx; subst.
        destruct (Minass_minimal _ _ _ Hδ) as [i [? ?]].
        destruct (Minass_minimal _ _ _ Hδ0) as [j [? ?]].
        unfold Minass_p, Minass_q in *.
        lia.
      * destruct H.
        inversion ctx_x; subst.
        inversion Hx; subst.
        destruct (Minass_minimal _ _ _ Hδ) as [i [? ?]].
        destruct (Minass_minimal _ _ _ Hδ0) as [j [? ?]].
        unfold Minass_p, Minass_q in *.
        lia.
  - simpl.
    eapply rst_trans.
    { onestepf. apply appsubst. }
    apply rst_refl_propositional.
    f_equal.
    all: f_equal.
    + apply cfcontext_irrelevance_Tm_of_Tmcf.
    + apply cfassign_irrelevance_Tms_of_Tmscf.
    + apply cfcontext_irrelevance_Tm_of_Tmcf.
    + apply cfassign_irrelevance_Tms_of_Tmscf.

Qed.

Lemma Tms_of_Tmscf_compatibility'' {pδ pσ qδ qσ:nat} {δ σ : Tmscf}
  (ass_δ : cfassign pδ qδ δ) (ass_σ : cfassign pσ qσ σ)
  (E_p : pσ = pδ)
  (E_q : qσ = qδ)
  (red : Tmscfσstep' δ σ)
  : (Tms_of_Tmscf δ ass_δ) <--s>*
    eq_rect pσ (fun p => Tms p qδ)
      (eq_rect qσ (Tms pσ) (Tms_of_Tmscf σ ass_σ) qδ E_q) pδ E_p.
Proof.
  revert pδ pσ qδ qσ ass_δ ass_σ E_p E_q.
  induction red; intros pδ pσ qδ qσ ass_δ ass_σ E_p E_q;
    destruct E_p; destruct E_q.
  - cbn [eq_rect].
    refine (rst_trans _ _ _
      (Tms_comp (Tms_of_Tmscf Tmscf_id (cfassign_id qσ)) (Tms_of_Tmscf δ ass_σ) )
      _ _ _).
    { apply rst_refl_propositional.
      apply Tms_of_Tmscf_ctc_comp.
      cbn.
      lia. }
    onestepf.
    apply idl.
  - cbn [eq_rect].
    refine (rst_trans _ _ _
      (Tms_comp (Tms_of_Tmscf δ ass_σ) (Tms_of_Tmscf Tmscf_id (cfassign_id pσ)) )
      _ _ _).
    { apply rst_refl_propositional.
      apply Tms_of_Tmscf_ctc_comp.
      destruct (Minass_minimal _ _ _ ass_σ) as [i [? ?]].
      unfold Minass_p, Minass_q; lia. }
    onestepf.
    apply idr.
  - cbn [eq_rect].
    eapply rst_trans.
    { simpl. onestepf. apply ass. }
    apply rst_refl_propositional.
    apply Tms_of_Tmscf_ctc_ass.
    + Minbeta. lia.
    + reflexivity.
  - cbn [eq_rect].
    destruct qσ.
    { exfalso. inversion ass_σ. }
    eapply rst_trans.
    { onestepf. apply snocomp. }

    refine (rst_trans _ _ _
      (Tms_snoc
      (Tms_comp (Tms_of_Tmscf δ _) (Tms_of_Tmscf σ _))
      (Tm_subst (Tm_of_Tmcf t _) (Tms_of_Tmscf σ _))) _ _ _).
    { apply rst_refl. }
    apply rst_sym.
    refine (rst_trans _ _ _
      (Tms_snoc
      (Tms_comp (Tms_of_Tmscf δ _) (Tms_of_Tmscf σ _))
      (Tm_subst (Tm_of_Tmcf t _) (Tms_of_Tmscf σ _))) _ _ _).
    { apply rst_refl. }
    apply rst_refl_propositional.
    inversion ass_δ; subst.
    inversion Hδ₁; subst.
    specialize (Minctx_minimal _ _ Hx); intro.
    destruct (Minass_minimal _ _ _ Hδ₂) as [i [? ?]].
    destruct (Minass_minimal _ _ _ Hδ) as [j [? ?]].
    apply Tms_of_Tmscf_ctc_snocomp.
    + Minbeta. unfold Minass_p, Minass_q, Minctx in *. lia.
    + Minbeta. unfold Minass_p, Minass_q, Minctx in *. lia.
  - cbn [eq_rect].
    eapply rst_trans.
    { onestepf. apply π₁beta. }
    apply rst_refl_propositional.
    apply cfassign_irrelevance_Tms_of_Tmscf.
  - cbn [eq_rect].
    eapply rst_trans.
    { apply π₁comp. }
    apply rst_refl_propositional.
    apply (f_equal Tms_π₁).
    apply Tms_of_Tmscf_ctc_comp.
    Minbeta.
    lia.
  - cbn [eq_rect].
    destruct qσ.
    { exfalso. inversion ass_δ. }
    cbn.
    eapply rst_trans.
    2:{ onestepf. apply πeta. }
    apply rst_refl_propositional.
    apply Tms_of_Tmscf_ctc_πeta.
    destruct (Minass_minimal _ _ _ ass_σ) as [j [? ?]].
    unfold Minass_p, Minass_q.
    lia.
Qed.

Fixpoint Tm_of_Tmcf_compatibility' {px py:nat} {x y : Tmcf}
  (ctx_x : cfcontext px x) (ctx_y : cfcontext py y)
  (E : py = px)
  (red : Tmcfσstep x y)
  : (Tm_of_Tmcf x ctx_x) <-->* eq_rect py Tm (Tm_of_Tmcf y ctx_y) _ E
with Tms_of_Tmscf_compatibility' {pδ pσ qδ qσ:nat} {δ σ : Tmscf}
  (ass_δ : cfassign pδ qδ δ) (ass_σ : cfassign pσ qσ σ)
  (E_p : pσ = pδ)
  (E_q : qσ = qδ)
  (red : Tmscfσstep δ σ)
  : (Tms_of_Tmscf δ ass_δ) <--s>*
    eq_rect pσ (fun p => Tms p qδ)
      (eq_rect qσ (Tms pσ) (Tms_of_Tmscf σ ass_σ) qδ E_q) pδ E_p.
Proof.
{ revert px py ctx_x ctx_y E.
  induction red; intros px py ctx_x ctx_y ; destruct E.
  - apply Tm_of_Tmcf_compatibility''.
    exact H.
  - simpl.
    specialize (IHred _ _ (contextof_subst ctx_x) (contextof_subst ctx_y) (eq_refl)).
    eapply rst_trans.
    { eapply (HINTsubst_Tm_step_compatibility).
      apply IHred. }
    eapply HINTsubst_Tms_step_compatibility.
    apply rst_refl_propositional.
    apply cfassign_irrelevance_Tms_of_Tmscf.
  - simpl.
    generalize (contextof_subst ctx_x) (contextof_subst ctx_y).
    intros ? ?.
    assert (E : Minass_q δ + (py - Minass_p δ)
      = Minass_q δ' + (py - Minass_p δ')).
    { inversion ctx_x.
      inversion ctx_y.
      eapply (Minass_conv_corollary H).
      - exact Hδ.
      - exact Hδ0. }
    apply (Tms_of_Tmscf_ctc_subst E).
    + destruct E.
      apply rst_refl_propositional.
      apply cfcontext_irrelevance_Tm_of_Tmcf.
    + apply (Tms_of_Tmscf_compatibility' _ _ _ _ _ _ _ _ (eq_refl) E H).
  - simpl.
    assert (E :
      pred (Minass_q δ + (py - Minass_p δ)) =
      pred (Minass_q δ' + (py - Minass_p δ'))).
    { inversion ctx_x.
      inversion ctx_y.
      destruct (Minass_conv_corollary H Hδ Hδ0).
      reflexivity. }
    simple refine (Tms_of_Tmscf_ctc_π₂ (assignof_π₂ ctx_x) (assignof_π₂ ctx_y) E _).
    generalize (assignof_π₂ ctx_x) (assignof_π₂ ctx_y).
    intros ? ?.
    destruct E.
    simpl.
    apply (Tms_of_Tmscf_compatibility' _ _ _ _ δ' δ _ _ eq_refl eq_refl H).
  - simpl.
    eapply rst_trans.
    { eapply HINT_rator_step_compatibility.
      apply (IHred _ _ _ (contextof_rator ctx_y) eq_refl). }
    apply HINT_rand_step_compatibility.
    apply rst_refl_propositional.
    apply cfcontext_irrelevance_Tm_of_Tmcf.
  - simpl.
    eapply rst_trans.
    { eapply HINT_rand_step_compatibility.
      apply (IHred _ _ _ (contextof_rand ctx_y) eq_refl). }
    apply HINT_rator_step_compatibility.
    apply rst_refl_propositional.
    apply cfcontext_irrelevance_Tm_of_Tmcf.
  - simpl.
    apply HINT_lam_step_compatibility.
    apply (IHred _ _ _ _ eq_refl).
}
{ revert pδ pσ qδ qσ ass_δ ass_σ E_p E_q.
  induction red; intros pδ pσ qδ qσ ass_δ ass_σ;
    destruct E_p; destruct E_q.
  - apply Tms_of_Tmscf_compatibility''.
    exact H.
  - cbn [eq_rect].
    destruct qσ.
    { exfalso. inversion ass_δ. }
    simpl.
    eapply rst_trans.
    { eapply HINTsnoc_Tms_step_compatibility.
      apply (IHred _ _ _ _ _ (assignof_snoc ass_σ) eq_refl eq_refl). }
    simpl.
    apply HINTsnoc_Tm_step_compatibility.
    apply rst_refl_propositional.
    apply cfcontext_irrelevance_Tm_of_Tmcf.
  - destruct qσ.
    { exfalso. inversion ass_δ. }
    simpl.
    eapply rst_trans.
    { eapply HINTsnoc_Tm_step_compatibility.
      apply (Tm_of_Tmcf_compatibility' _ _ _ _ _ (contextof_snoc ass_σ) eq_refl H). }
    apply HINTsnoc_Tms_step_compatibility.
    apply rst_refl_propositional.
    apply cfassign_irrelevance_Tms_of_Tmscf.
  - simpl.
    assert (E
      : Minass_p δ + (qσ - Minass_q δ)
      = Minass_p δ' + (qσ - Minass_q δ')).
    { inversion ass_δ.
      inversion ass_σ.
      exact (Minass_conv_corollary' red Hδ₁ Hδ₁0). }
    eapply rst_trans.
    { eapply HINT_compl_step_compatibility.
      exact (IHred _ _ _ _ (assignlof_comp ass_δ) (assignlof_comp ass_σ) E eq_refl). }
    generalize (assignrof_comp ass_δ) (assignrof_comp ass_σ).
    intros ? ?.
    destruct E.
    simpl.
    apply HINT_compr_step_compatibility.
    apply rst_refl_propositional.
    apply cfassign_irrelevance_Tms_of_Tmscf.
  - simpl.
    eapply rst_trans.
    { eapply HINT_compr_step_compatibility.
      refine (IHred _ _ _ _ (assignrof_comp ass_δ) (assignrof_comp ass_σ) eq_refl eq_refl). }
    apply HINT_compl_step_compatibility.
    apply rst_refl_propositional.
    apply cfassign_irrelevance_Tms_of_Tmscf.
  - simpl.
    apply HINT_π₁_step_compatibility.
    apply (IHred _ _ _ _ _ (assignof_π₁ ass_σ) eq_refl eq_refl).
}
Qed.

Lemma Tm_of_Tmcf_compatibility {px py:nat} {x y : Tmcf}
  (ctx_x : cfcontext px x) (ctx_y : cfcontext py y)
  (E : py = px)
  (red : (x -->* y)%AKcf)
  : (Tm_of_Tmcf x ctx_x) <-->* eq_rect py Tm (Tm_of_Tmcf y ctx_y) _ E.
Proof.
  induction red.
  - apply Tm_of_Tmcf_compatibility'.
    exact H.
  - destruct E.
    simpl.
    apply rst_refl_propositional.
    apply cfcontext_irrelevance_Tm_of_Tmcf.
  - destruct E.
    simpl in *.
    eapply rst_trans.
    + refine (IHred1 _ _).
      apply (cfcontext_preserved red1).
      exact ctx_x.
    + apply IHred2.
Qed.

Lemma Tms_of_Tmscf_compatibility {pδ pσ qδ qσ:nat} {δ σ : Tmscf}
  (ass_δ : cfassign pδ qδ δ) (ass_σ : cfassign pσ qσ σ)
  (E_p : pσ = pδ)
  (E_q : qσ = qδ)
  (red : (δ --s>* σ)%AKcf)
  : (Tms_of_Tmscf δ ass_δ) <--s>*
    eq_rect pσ (fun p => Tms p qδ)
      (eq_rect qσ (Tms pσ) (Tms_of_Tmscf σ ass_σ) qδ E_q) pδ E_p.
Proof.
  simpl.
  induction red.
  - apply Tms_of_Tmscf_compatibility'.
    exact H.
  - destruct E_p.
    destruct E_q.
    simpl.
    apply rst_refl_propositional.
    apply cfassign_irrelevance_Tms_of_Tmscf.
  - destruct E_p.
    destruct E_q.
    simpl in *.
    eapply rst_trans.
    + refine (IHred1 _ _).
      apply (cfassign_preserved red1).
      exact ass_δ.
    + apply IHred2.
Qed.

Lemma Tm_of_Tmcf_compatibility0 {p :nat} {x y : Tmcf}
  (ctx_x : cfcontext p x) (ctx_y : cfcontext p y)
  (red : (x -->* y)%AKcf)
  : (Tm_of_Tmcf x ctx_x) <-->* (Tm_of_Tmcf y ctx_y).
Proof.
  apply (Tm_of_Tmcf_compatibility _ _ eq_refl).
  exact red.
Qed.

Lemma Tms_of_Tmscf_compatibility0 {p q :nat} {δ σ : Tmscf}
  (ass_δ : cfassign p q δ) (ass_σ : cfassign p q σ)
  (red : (δ --s>* σ)%AKcf)
  : (Tms_of_Tmscf δ ass_δ) <--s>* (Tms_of_Tmscf σ ass_σ).
Proof.
  apply (Tms_of_Tmscf_compatibility _ _ eq_refl eq_refl).
  exact red.
Qed.

End AKcf_to_AK_Compatibility.

Fixpoint TmcfTm_immersion {p:nat} (x :Tmcf) (Hx:cfcontext p x)
  : Tmcf_of_Tm (Tm_of_Tmcf x Hx) = x
with TmcfsTms_immersion {p0 q0 : nat} (δ : Tmscf) (pqδ : cfassign p0 q0 δ)
  : Tmscf_of_Tms (Tms_of_Tmscf δ pqδ) = δ.
Proof.
{ revert p Hx.
  induction x as [x IH δ| δ | x IHx | x IH]; intros p Hx.
  + simpl.
    f_equal.
    - apply IH.
    - apply TmcfsTms_immersion.
  + simpl.
    f_equal.
    apply TmcfsTms_immersion.
  + simpl.
    f_equal.
    - apply IHx.
    - apply IHx1.
  + simpl.
    f_equal.
    apply IH.
}
{ revert p0 q0 pqδ.
  induction δ as [δ IH x0 | | δ₁ IHδ1 δ₂ IHδ2 | ? ]; intros p0 q0 pqδ.
  + destruct q0.
    { exfalso. exact (contextof_snoc_false pqδ). }
    simpl.
    f_equal.
    - apply IH.
    - apply TmcfTm_immersion.
  + simpl.
    destruct (contextof_id pqδ).
    reflexivity.
  + simpl.
    f_equal.
    - apply IHδ1.
    - apply IHδ2.
  + simpl.
    f_equal.
    apply IHδ.
}
Qed.

Fixpoint TmTmcf_immersion' {p p':nat} (x :Tm p)
  (ctx : cfcontext p' (Tmcf_of_Tm x)) (E_p : p = p')
  : Tm_of_Tmcf (Tmcf_of_Tm x) ctx <-->*
    eq_rect p Tm x p' E_p
with TmsTmscf_immersion' {p p' q q' : nat} (δ : Tms p q)
  (ass : cfassign p' q' (Tmscf_of_Tms δ))
  (E_p : p = p')
  (E_q : q = q')
  : Tms_of_Tmscf (Tmscf_of_Tms δ) ass <--s>*
    eq_rect p (fun p => Tms p q') (eq_rect q (Tms p) δ q' E_q) p' E_p.
Proof.
{ induction x; destruct E_p.
  - assert (EE : q = Minass_q (Tmscf_of_Tms δ) + (p - Minass_p (Tmscf_of_Tms δ))).
    { subst.
      destruct (Minass_minimal _ _ _ (assignFromTms δ)) as [i [? ?]].
      unfold Minass_p, Minass_q.
      lia. }
    simpl.
    eapply rst_trans.
    { eapply HINTsubst_Tm_step_compatibility.
      refine (TmTmcf_immersion' _ _ x _ EE). }
    eapply rst_trans.
    { eapply HINTsubst_Tms_step_compatibility.
      refine (TmsTmscf_immersion' _ _ _ _ δ _ (eq_refl p) EE). }
    destruct EE.
    apply rst_refl.
  - assert (EE : q = pred (Minass_q (Tmscf_of_Tms δ) + (p - Minass_p (Tmscf_of_Tms δ)))).
    { subst.
      destruct (Minass_minimal _ _ _ (assignFromTms δ)) as [i [? ?]].
      unfold Minass_p, Minass_q.
      lia. }
    simpl.
    eapply rst_trans.
    { eapply HINT_π₂_step_compatibility.
      refine (TmsTmscf_immersion' _ _ _ _ δ _ _ _).
      - reflexivity.
      - apply eq_S.
        exact EE. }
    simpl.
    destruct EE.
    apply rst_refl.
  - simpl.
    eapply rst_trans.
    { eapply HINT_rator_step_compatibility.
      refine (TmTmcf_immersion' _ _ x1 _ (eq_refl p)). }
    eapply HINT_rand_step_compatibility.
    refine (TmTmcf_immersion' _ _ x2 _ (eq_refl p)).
  - simpl.
    eapply rst_trans.
    { eapply HINT_lam_step_compatibility.
      refine (TmTmcf_immersion' _ _ x _ (eq_refl (S p))). }
    apply rst_refl.
}
{ induction δ; destruct E_p; destruct E_q.
  - onestepf.
    apply nileta.
  - simpl.
    eapply rst_trans.
    { eapply HINTsnoc_Tm_step_compatibility.
      refine (TmTmcf_immersion' _ _ x _ (eq_refl p)). }
    eapply HINTsnoc_Tms_step_compatibility.
    refine (TmsTmscf_immersion' _ _ _ _ δ _ (eq_refl p) (eq_refl q)).
  - destruct (proof_irrelevance _ (cfassign_id p) ass).
    apply rst_refl.
  - assert (EE : q = Minass_p (Tmscf_of_Tms δ1) + (r - Minass_q (Tmscf_of_Tms δ1))).
    { subst.
      destruct (Minass_minimal _ _ _ (assignFromTms δ1)) as [i [? ?]].
      unfold Minass_p, Minass_q.
      lia. }
    simpl.
    eapply rst_trans.
    { eapply HINT_compl_step_compatibility.
      refine (TmsTmscf_immersion' _ _ _ _ δ1 _ EE (eq_refl r)). }
    eapply rst_trans.
    { eapply HINT_compr_step_compatibility.
      refine (TmsTmscf_immersion' _ _ _ _ δ2 _ (eq_refl p) EE). }
    destruct EE.
    apply rst_refl.
  - simpl.
    eapply rst_trans.
    { eapply HINT_π₁_step_compatibility.
      refine (TmsTmscf_immersion' _ _ _ _ δ _ (eq_refl p) (eq_refl (S q))). }
    apply rst_refl.
}
Qed.

Theorem TmTmcf_immersion {p:nat} (x :Tm p)
  : (Tm_of_Tmcf (Tmcf_of_Tm x) (contextFromTm x) <-->* x).
Proof.
  apply (TmTmcf_immersion' _ _ (eq_refl _)).
Defined.

Theorem TmsTmscf_immersion {p q : nat} (δ : Tms p q)
  : ((Tms_of_Tmscf (Tmscf_of_Tms δ) (assignFromTms δ)) <--s>* δ).
Proof.
  apply (TmsTmscf_immersion' _ _ (eq_refl _) (eq_refl _)).
Defined.