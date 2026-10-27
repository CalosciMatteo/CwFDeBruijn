From CwFdeBruijn.Syntax.AKcf Require Export Conv_Lemmas values occur_Lemmas.



Theorem subst_cf_iter_lift_id {t:Tmcf} (tV : Tmcfσvalue t) (i:nat) : Tmcf_subst t (iter_lift i Tmscf_id) -->* t.
Proof.
  revert i.
  induction tV; intros i.
  - destruct (cf_iter_π₁idP_to_cf_iter_π₁id Hδ) as [j ?]; subst.
    eapply rt_trans. { onestep. apply cf_substπ₂. }
    destruct (le_lt_dec j i) as [leq|lt].
    + eapply rt_trans.
      { eapply HINTcf_π₂_step_compatibility.
        apply Tmscf_compiterπid. }
      apply cf_iter_π₂_lift_id.
      exact leq.
    + apply HINTcf_π₂_step_compatibility.
      eapply rt_trans. { apply Tmscf_compiterπid. }
      apply cf_iter_π₁_more_lift_id.
      exact lt.
  - eapply rt_trans.
    { onestep.
      apply cf_appsubst. }
    eapply rt_trans.
    { eapply HINTcf_rator_step_compatibility.
      apply IHtV1. }
    eapply HINTcf_rand_step_compatibility.
    apply IHtV2.
  - eapply rt_trans.
    { onestep. apply cf_lamsubst. }
    apply HINTcf_lam_step_compatibility.
    apply (IHtV (S i)).
Qed.

Theorem subst_cf_lift_id {t:Tmcf} (tV : Tmcfσvalue t)
: Tmcf_subst t (lift Tmscf_id) -->* t.
Proof.
  exact (subst_cf_iter_lift_id tV 1).
Qed.

Theorem V_subst_id {t:Tmcf} (tV : Tmcfσvalue t)
: Tmcf_subst t Tmscf_id -->* t.
Proof.
  exact (subst_cf_iter_lift_id tV 0).
Qed.

Theorem subst_id {t:Tmcf}
: Tmcf_subst t Tmscf_id <-->* t.
Proof.
  destruct (Tmcf_normalization t) as [t0 [tred t0nf]].
  eapply rst_trans with (Tmcf_subst t0 Tmscf_id).
  { apply clos_rt_clos_rst. autored. }
  eapply rst_trans with t0.
  { apply clos_rt_clos_rst.
    apply V_subst_id.
    apply (Tmcfσnf_is_value t0nf). }
  apply rst_sym. 
  apply clos_rt_clos_rst.
  exact tred.
Qed.
(* Note:
  [[ (Tmcf_subst t (Tmscf_id)) -->* t ]]
  does not hold for arbitrary terms:
  take t := Tmcf_π₂ (Tmscf_snoc δ (Tmcf_ref 0)). *)
