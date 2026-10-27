From Stdlib Require Import Nat PeanoNat Lia.

From Category Require Import Lib Theory.
From Category.Construction Require Import Opposite.
From Category.Functor Require Import Product Hom.
From Category.Instance Require Import
  Sets Sets.Cartesian
  Fun Fun.Cartesian.

From CwFdeBruijn Require Import
  CatPsh Uwcwf MwM
  Contextual

  Construction.Monoidification.SubstRel
  Construction.Monoidification.TmRel
  Construction.Monoidification.Compose
  Construction.Monoidification.Substitution
  Construction.Monoidification.CwP
  Construction.Monoidification.CtxCmp.Snoc
  
  Structure.FlippedComprehension
  Structure.FlippedComprehension.IterUpshift
  Structure.FlippedComprehension.IterTmUpshift
  Structure.FlippedComprehension.IterUpshiftSnoc.

Section CtxComprehension.
Context {C : UWCwFN}.

Section π1.
Definition Mndf_π1 (δ : @Mndf_S_carrier C) : @Mndf_S_carrier C
  := Build_Mndf_S_carrier (π1 (↑(Mndf_S_rep δ))).

#[global]
Instance Mndf_T_π1_respects :
  Proper (equiv ==> equiv)
    (@Mndf_π1).
Proof.
  intros δ δ' [r1 r2 m n Er1m Er1n Er2m Er2n E].
  unfold Mndf_π1.
  eapply (Build_Mndf_S_rel _ _ r1 r2).
  simpl.
  erewrite <-!pi1_iter_upshift_Eq.
  erewrite <-!iter_upshift_Eq_swap.
  erewrite !iter_upshift_Eq_beta_S.
  f_equiv.
  f_equiv.
  exact E.
  Unshelve.
  all: simpl;
    apply nnp_l_injective;
    specialize (f_equal nnp_l Er1m);
    specialize (f_equal nnp_l Er1n);
    specialize (f_equal nnp_l Er2m);
    specialize (f_equal nnp_l Er2n);
    repeat rewrite ?nnp_l_iter, ?nnp_l_s;
    try lia.
Qed.

Lemma Mndf_π1_carrier {m n} (δ : m ~> s n)
  : Mndf_π1 (Build_Mndf_S_carrier δ) ≈ Build_Mndf_S_carrier (π1 δ).
Proof.
  eapply (Build_Mndf_S_rel _ _ 0 1).
  simpl.
  erewrite iter_upshift_Eq_beta_S.
  rewrite !iter_upshift_Eq_beta_0.
  apply pi1_upshift.
  Unshelve.
  all: reflexivity.
Qed.

End π1.

Section π2.
Definition Mndf_π2 (δ : @Mndf_S_carrier C) : @Mndf_T_carrier C
  := Build_Mndf_T_carrier (π2 (↑(Mndf_S_rep δ))).

#[global]
Instance Mndf_T_π2_respects :
  Proper (equiv ==> equiv)
    (@Mndf_π2).
Proof.
  intros δ δ' [r1 r2 m n Er1m Er1n Er2m Er2n E].
  unfold Mndf_π2.
  eapply (Build_Mndf_T_rel _ _ r1 r2).
  simpl.
  erewrite <-!pi2_iter_upshift_Eq.
  erewrite <-!iter_upshift_Eq_swap.
  erewrite !iter_upshift_Eq_beta_S.
  f_equiv.
  f_equiv.
  exact E.
  Unshelve.
  all: simpl;
    apply nnp_l_injective;
    specialize (f_equal nnp_l Er1m);
    specialize (f_equal nnp_l Er1n);
    specialize (f_equal nnp_l Er2m);
    specialize (f_equal nnp_l Er2n);
    repeat rewrite ?nnp_l_iter, ?nnp_l_s;
    try lia.
Qed.

Lemma Mndf_π2_carrier {m n} (δ : m ~> s n)
  : Mndf_π2 (Build_Mndf_S_carrier δ) ≈ Build_Mndf_T_carrier (π2 δ).
Proof.
  eapply (Build_Mndf_T_rel _ _ 0 1).
  simpl.
  erewrite iter_Tm_upshift_Eq_beta_S.
  rewrite !iter_Tm_upshift_Eq_beta_0.
  apply pi2_upshift.
  Unshelve.
  all: reflexivity.
Qed.

End π2.

Context (n : Mndf_CwP C).

Program Definition Mndf_snoc_ntr
  : [Hom ─ , n ] × Tm ⟹ [Hom ─ , n ]
  := Build_Transform'
    (λ m , Mndf_snoc_setoidmorphism
      : fobj[ [Hom ─ , n ] × Tm] m ~{ Sets }~> fobj[[Hom ─ , n ]] m)
    _.
Final Obligation.
  revert f m m0; intros γ δ a.
  change Mndf_S_rel with (@equiv (@Mndf_S_carrier C) _).

  set (r := max_ctx (max_ctx (Mndf_T_m a) (Mndf_S_n γ))(Mndf_S_m δ)).
  set (ia := nnp_l r - nnp_l (Mndf_T_m a)).
  set (iγ := nnp_l r - nnp_l (Mndf_S_n γ)).
  set (iδ := nnp_l r - nnp_l (Mndf_S_m δ)).

  assert (Eγa : iter iγ s (Mndf_S_n γ) = iter ia s (Mndf_T_m a)).
  2: assert (Eδa : iter iδ s (Mndf_S_m δ) = iter ia s (Mndf_T_m a)).
  1-2: abstract (apply nnp_l_injective;
    unfold iγ, iδ, ia, r;
    repeat rewrite ?nnp_l_iter, ?nnp_l_s, ?nnp_l_max;
    lia).

  erewrite (Mndf_T_rel_iter_upshift_Eq a ia eq_refl).
  erewrite (Mndf_S_rel_iter_upshift_Eq γ iγ eq_refl Eγa).
  erewrite (Mndf_S_rel_iter_upshift_Eq δ iδ Eδa eq_refl).

  rewrite Mndf_snoc_matching_ctx.
  rewrite Mndf_S_compose_matching_ctx.
  rewrite Mndf_S_compose_matching_ctx.
  rewrite Mndf_T_subst_matching_ctx.
  rewrite Mndf_snoc_matching_ctx.

  apply make_Mndf_S_rel_samectx.
  
  rewrite snoc_comp.
  reflexivity.
Qed.

Program Definition Mndf_π1_ntr : [Hom ─ , n ] ~> [Hom ─ , n ]
  := Build_Transform'
    (λ m,  {|morphism := Mndf_π1|}
      : fobj[[Hom ─ , n ]] m  ~{ Sets }~> fobj[[Hom ─ , n ]] m) 
    _.
Final Obligation.
  revert f x0; intros δ γ.
  change Mndf_S_rel with (@equiv (@Mndf_S_carrier C) _).
  etransitivity.
  { eapply (Mndf_S_compose'_rew _ _ _ _ _ _ _ _ _ _ _
      (s (Mndf_S_m (Mndf_S_compose γ δ)))
      _
      (Mndf_S_n (Mndf_S_compose γ δ))). }

  apply make_Mndf_S_rel_samectx.

  unfold Mndf_π1, Mndf_S_compose, Mndf_S_compose'; cbn [Mndf_S_rep].
  erewrite <-pi1_iter_upshift_Eq.
  rewrite pi1_comp.
  erewrite <-(iter_upshift_Eq_swap _ _ _ _ _ (Mndf_S_rep γ)).
  erewrite (iter_upshift_Eq_beta_S _ _ _ _ _ (Mndf_S_rep δ)).
  erewrite iter_upshift_Eq_beta_S.
  rewrite <-upshift_comp.
  f_equiv; f_equiv.
  Unshelve.
    all: simpl;
      apply nnp_l_injective;
      unfold max_ctx_diff_r, max_ctx_diff_l;
      repeat rewrite ?nnp_l_max, ?nnp_l_iter, ?nnp_l_s;
      try lia.
Qed.

Program Definition Mndf_π2_ntr : [Hom ─ , n ] ~> Tm
  := Build_Transform'
    (λ m,  {|morphism := Mndf_π2|}
      : fobj[[Hom ─ , n ]] m  ~{ Sets }~> fobj[Tm] m) 
    _.
Final Obligation.
  revert f x0; intros δ γ.
  unfold Mndf_T_subst, Mndf_π2.
  change Mndf_T_rel with (@equiv (@Mndf_T_carrier C) _).
  etransitivity.
  { eapply (Mndf_T_subst'_rew _ _ _ _ _ _ _ _ _ (s (Mndf_S_m (Mndf_S_compose γ δ)))). }
  unfold Mndf_T_subst'.
  apply make_Mndf_T_rel_samectx.
  cbn [Mndf_T_rep].
  erewrite <-pi2_iter_upshift_Eq.
  rewrite pi2_subst.
  erewrite <-(iter_upshift_Eq_swap _ _ _ _ _ (Mndf_S_rep γ)).
  erewrite (iter_upshift_Eq_beta_S _ _ _ _ _ (Mndf_S_rep δ)).
  erewrite iter_upshift_Eq_beta_S.
  rewrite <-upshift_comp.
  f_equiv; f_equiv.
  unfold Mndf_S_compose, Mndf_S_compose'.
  cbn [Mndf_S_rep].
  reflexivity.

  Unshelve.
    all: simpl;
      apply nnp_l_injective;
      unfold max_ctx_diff_r, max_ctx_diff_l;
      repeat rewrite ?nnp_l_max, ?nnp_l_iter, ?nnp_l_s;
      try lia.
Qed.

Definition Mndf_π1π2 : [Hom ─ , n ] ⟹ [Hom ─ , n ] × Tm
  := Mndf_π1_ntr △ Mndf_π2_ntr.

Section iso.

Program Definition Mndf_ctxcmp : [Hom ─ , n ] × Tm ≅ [Hom ─ , n ] :=
{|
  to := Mndf_snoc_ntr;
  from := Mndf_π1π2;
|}.
Next Obligation.
  revert x0; intros δ.
  change Mndf_S_rel with (@equiv (@Mndf_S_carrier C) _).
  rewrite Mndf_S_compose_id_right.

  rewrite Mndf_snoc_matching_ctx.
  eapply (Build_Mndf_S_rel _ _ 0 1).
  erewrite iter_upshift_Eq_swap.
  rewrite !iter_upshift_Eq_beta_0.
  simpl.
  rewrite <-snoc_eta.
  reflexivity.

  Unshelve.
  all: reflexivity.
Qed.
Final Obligation.
  revert m m0; intros δ a.
  change Mndf_S_rel with (@equiv (@Mndf_S_carrier C) _).
  change Mndf_T_rel with (@equiv (@Mndf_T_carrier C) _).

  set (r := max_ctx (Mndf_S_m δ) (Mndf_T_m a)).
  set (ia := nnp_l r - nnp_l (Mndf_T_m a)).
  set (iδ := nnp_l r - nnp_l (Mndf_S_m δ)).
  assert (E : iter iδ s (Mndf_S_m δ) = iter ia s (Mndf_T_m a)). { 
    apply nnp_l_injective;
      unfold iδ, ia, r;
      repeat rewrite ?nnp_l_iter, ?nnp_l_s, ?nnp_l_max;
      lia.
  }

  split.
  - rewrite Mndf_S_compose_id_right.
    erewrite (Mndf_T_rel_iter_upshift_Eq a ia eq_refl).
    erewrite (Mndf_S_rel_iter_upshift_Eq δ iδ E eq_refl).
    rewrite Mndf_snoc_matching_ctx.
    rewrite Mndf_π1_carrier.
    apply make_Mndf_S_rel_samectx.
    rewrite pi1_snoc.
    reflexivity.
  - rewrite Mndf_T_subst_id.
    erewrite (Mndf_T_rel_iter_upshift_Eq a ia eq_refl).
    erewrite (Mndf_S_rel_iter_upshift_Eq δ iδ E eq_refl).
    rewrite Mndf_snoc_matching_ctx.
    rewrite Mndf_π2_carrier.
    apply make_Mndf_T_rel_samectx.
    rewrite pi2_snoc.
    reflexivity.
Qed.

End iso.

End CtxComprehension.

Section uwcwf.
Context (C : UWCwFN).


Program Definition Mndf_UnitypedWeakCwF : @UnitypedWeakCwF (Mndf_CwP C) :={|
  distobj := tt;
  ctxext := λ Γ, Γ;
  ctxcmp := λ n, Mndf_ctxcmp n
|}.

Definition Mndf_UWCwF : UWCwF := (Mndf_CwP C ; Mndf_UnitypedWeakCwF).

Program Instance Mndf_UWCwF_MonoidWithModule : @MonoidWithModule (Mndf_UWCwF ) := {|
  hasSingleContext := _;
|}.

Definition Mndf_MwM : MwM := ((Mndf_UWCwF ) ; Mndf_UWCwF_MonoidWithModule).

End uwcwf.

