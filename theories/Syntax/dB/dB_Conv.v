From CwFdeBruijn.Syntax.dB Require Export dB substLemmas.
From Stdlib Require Export Relations.

Declare Scope dB.
Open Scope dB.
Delimit Scope dB with dB.

Reserved Notation " x '-->' x' " (at level 55, x' at level 55).

Inductive dB_step : relation dB :=
  | dB_beta {x y} : (dB_app (dB_lam x) y) --> (dB_subst (dB_snoc (dB_ref) y) x)
  | dB_rator_step {x' x y} : x' --> x -> (dB_app x' y) --> (dB_app x y)
  | dB_rand_step {x y' y} : y' --> y -> (dB_app x y') --> (dB_app x y)
  | dB_lam_step {x' x} : x' -->  x -> (dB_lam x') --> (dB_lam x)
where " x '-->' x' " := (dB_step x x').

Definition dB_conv := clos_refl_trans dB dB_step.
Notation " x '-->*' x' " := (dB_conv x x') (at level 55, x' at level 55) : dB.

Record dB_compatible (R : dB -> dB -> Prop) := make_dB_compatible {
  dB_rator_compatibility {x' x y} : R x' x -> R (dB_app x' y) (dB_app x y);
  dB_rand_compatibility {x y' y} : R y' y -> R (dB_app x y') (dB_app x y);
  dB_lam_compatibility {x' x} : R x' x -> R (dB_lam x') (dB_lam x)
}.

Theorem dB_conv_compatibility : dB_compatible dB_conv.
Proof.
  split.
  + intros x' x y H.
    induction H.
    - apply rt_step.
      apply dB_rator_step.
      exact H.
    - apply rt_refl.
    - apply (rt_trans _ _ _  (dB_app y0 y)); assumption.
  + intros x y' y H.
    induction H.
    - apply rt_step.
      apply dB_rand_step.
      exact H.
    - apply rt_refl.
    - apply (rt_trans _ _ _  (dB_app x y)); assumption.
  + intros x' x H.
    induction H.
    - apply rt_step.
      apply dB_lam_step.
      assumption.
    - apply rt_refl.
    - apply (rt_trans _ _ _  (dB_lam y)); assumption.
Qed.

Lemma dB_subst_compatibility δ x' x : x' -->* x -> dB_subst δ x' -->* dB_subst δ x.
Proof.
  intro H.
  induction H.
  - revert δ.
    induction H; intros δ.
    + simpl.
      refine (rt_trans _ _ _ _ _ _ _).
      {
        apply rt_step.
        apply dB_beta.
      }
      fold dB_conv.
      revert δ.
      induction x; simpl; intros δ.
      * induction i.
      ** apply rt_refl.
      **  simpl.
          rewrite subst_snoc_ref_reind_id.
          apply rt_refl.
      * refine (rt_trans _ _ _ _ _ _ _).
        { apply dB_rand_compatibility.
          {exact dB_conv_compatibility. }
          apply IHx2.
        }
        refine (rt_trans _ _ _ _ _ _ _).
        { apply dB_rator_compatibility.
          {exact dB_conv_compatibility. }
          apply IHx1.
        }
        apply rt_refl.
      *
        apply dB_lam_compatibility.
        {exact dB_conv_compatibility. }

        assert (
          dB_subst
            (lift (dB_snoc dB_ref (dB_subst δ y)))
            (dB_subst (lift (lift δ)) x) =
          dB_subst
            (lift δ)
            (dB_subst (lift (dB_snoc dB_ref y)) x)
        ).
        {
          rewrite !dB_subst_subst.
          f_equal.
          rewrite !lift_assign_comp.
          f_equal.
          unfold assign_comp.
          apply extensionality.
          intro i.
          induction i.
          + reflexivity.
          + cbn.
            apply subst_snoc_ref_reind_id.
        }
        rewrite H.
        apply rt_refl.
    + simpl.
      apply dB_rator_compatibility. {exact dB_conv_compatibility. }
      exact (IHdB_step δ).
    + simpl.
      apply dB_rand_compatibility. {exact dB_conv_compatibility. }
      exact (IHdB_step δ).
    + simpl.
      apply dB_lam_compatibility. {exact dB_conv_compatibility. }
      exact (IHdB_step (lift δ)).
  - apply rt_refl.
  - refine (rt_trans _ _ _ _ _ _ _).
    {apply IHclos_refl_trans1. }
    {apply IHclos_refl_trans2. }
Qed.