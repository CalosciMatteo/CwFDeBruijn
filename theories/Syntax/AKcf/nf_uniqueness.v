From CwFdeBruijn.Syntax.Immersions Require Import dBToAKcf.
From CwFdeBruijn.Syntax.AKcf Require Export GenRewr.

Open Scope AKcf.

Lemma Tmcf_nf_uniqueness : normal_form_uniqueness Tmcfσstep.
Proof.
  intros x y z y_nf z_nf xredy xredz.
  assert (E : dB_of_Tmcf y = dB_of_Tmcf z).
  { eapply eq_trans with (dB_of_Tmcf x).
    - symmetry.
      apply Tmcfσsoundness.
      exact xredy.
    - apply Tmcfσsoundness.
      exact xredz.
  }
  rewrite <-(TmcfDB_immersion_V (Tmcfσnf_is_value y_nf)).
  rewrite <-(TmcfDB_immersion_V (Tmcfσnf_is_value z_nf)).
  destruct E.
  reflexivity.
Qed.

(* Corollary *)
Lemma Tmcfσstep_bwtr {x y z : Tmcf}
  (z_nf : normal_form Tmcfσstep z)
  (xredz : x -->* z) (xredy : x -->* y)
  : y -->* z.
Proof.
  destruct (Tmcf_normalization y) as [z0 [yredz0 z0_nf]].
  assert (E: z = z0).
  { eapply Tmcf_nf_uniqueness; try assumption.
    - exact xredz.
    - eapply rt_trans.
      + exact xredy.
      + exact yredz0. }
  destruct E.
  exact yredz0.
Qed.

Lemma Tmcfσconv_spec (x y : Tmcf)
  : reflect
      (x <-->* y)    
      (Tmcf_beq (nffun (Tmcf_normalization x)) (nffun (Tmcf_normalization y))).
Proof.
  apply iff_reflect.
  apply iff_sym.
  rewrite <-(reflect_iff _ _ (Tmcf_eq_spec _ _)).
  apply (nfuniqueness_iff_conv Tmcf_nf_uniqueness Tmcf_normalization).
Qed.

Lemma Tmscfσconv_spec (δ σ : Tmscf)
  : reflect
      (δ <--s>* σ)    
      (Tmscf_beq (nffun (Tmscf_normalization δ)) (nffun (Tmscf_normalization σ))).
Proof.
  apply iff_reflect.
  apply iff_sym.
  rewrite <-(reflect_iff _ _ (Tmscf_eq_spec _ _)).
  apply (nfuniqueness_iff_conv Tmscf_nf_uniqueness Tmscf_normalization).
Qed.

Lemma Tmscf_nf_uniqueness : normal_form_uniqueness Tmscfσstep.
Proof.
  intros δ σ τ σ_nf τ_nf δredσ δredτ.
  assert (E : assign_of_tmscf σ = assign_of_tmscf τ).
  { eapply eq_trans with (assign_of_tmscf δ).
    - symmetry.
      apply (Tmscfσsoundness δredσ).
    - apply (Tmscfσsoundness δredτ).
  }
  erewrite <-(TmscfDB_immersion_V  (cfassign_preserved δredσ (Minass_ass δ)) (Tmscfσnf_is_value σ σ_nf)).
  erewrite <-(TmscfDB_immersion_V  (cfassign_preserved δredτ (Minass_ass δ)) (Tmscfσnf_is_value τ τ_nf)).
  destruct E.
  reflexivity.
Qed.

Lemma Tmscfσstep_bwtr {δ γ δnf : Tmscf}
  (δnf_is : normal_form Tmscfσstep δnf)
  (xredz : δ --s>* δnf) (xredy : δ --s>* γ)
  : γ --s>* δnf.
Proof.
  destruct (Tmscf_normalization γ) as [z0 [yredz0 z0_nf]].
  assert (E: δnf = z0).
  { eapply Tmscf_nf_uniqueness; try assumption.
    - exact xredz.
    - eapply rt_trans.
      + exact xredy.
      + exact yredz0. }
  destruct E.
  exact yredz0.
Qed.

Lemma nffun_Tmcf_app {a b}
  : nffun (Tmcf_normalization (Tmcf_app a b)) =
    Tmcf_app (nffun (Tmcf_normalization a)) (nffun (Tmcf_normalization b)) .
Proof.
  destruct (Tmcf_normalization (a @ b)%AKcf) as [abnf [abnf_red abnf_is]].
  destruct (Tmcf_normalization b) as [bnf [bnf_red bnf_is]].
  destruct (Tmcf_normalization a) as [anf [anf_red anf_is]].
  simpl.
  apply (Tmcf_nf_uniqueness (a@b) abnf (anf @ bnf)).
  { assumption. }
  { apply Tmcfσvalue_is_nf.
    constructor; apply Tmcfσnf_is_value; assumption. }
  { assumption. }
  now rewrite bnf_red, anf_red.
Qed.

Lemma nffun_Tmcf_lam {a}
  : nffun (Tmcf_normalization (λ a)) =
    λ (nffun (Tmcf_normalization a)).
Proof.
  destruct (Tmcf_normalization (λ a)) as [lanf [lanf_red lanf_is]].
  destruct (Tmcf_normalization a) as [anf [anf_red anf_is]].
  simpl.
  apply (Tmcf_nf_uniqueness (λ a) lanf (λ anf)).
  { assumption. }
  { apply Tmcfσvalue_is_nf.
    constructor; apply Tmcfσnf_is_value; assumption. }
  { assumption. }
  now rewrite anf_red.
Qed.

Lemma Tmcfσeq_from_lam a' a (H:λ a' <-->* λ a) : a' <-->* a.
Proof.
  unshelve eassert (e:=(proj2 (nfuniqueness_iff_conv _ _ _ _) H)).
  { apply Tmcf_nf_uniqueness. }
  { apply Tmcf_normalization. }
  rewrite !nffun_Tmcf_lam in e.
  inversion e.
  eapply (proj1 (nfuniqueness_iff_conv _ _ _ _)).
  apply H1.
  Unshelve.
  { apply Tmcf_nf_uniqueness. }
Qed.