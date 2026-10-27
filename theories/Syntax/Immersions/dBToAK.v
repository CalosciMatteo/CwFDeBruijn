From CwFdeBruijn.Syntax.Immersions Require Export dBToAKcf AKcfToAK.
From CwFdeBruijn.Syntax.AK Require Export AK_Conv.

Definition dB_of_Tm {p:nat} (x : AK.Tm p) : dB.dB.
Proof.
  apply dB_of_Tmcf.
  apply (Tmcf_of_Tm x).
Defined.

Definition Tm_of_dB (x : dB) : forall p (Hx : TmP p x), Tm p.
Proof.
  intros p H.
  simple refine (Tm_of_Tmcf _ _).
  { exact (Tmcf_of_dB x). }
  exact (cfcontext_Tmcf_of_dB H).
Defined.

Definition Tms_of_Assign q (δ : nat -> dB) :
    forall p (Hδ : TmsP p q δ), Tms p q.
Proof.
  intros.
  apply (Tms_of_Tmscf (Tmscf_of_Assign _ Hδ)).
  apply cfassign_Tmscf_of_assign.
Defined.

Theorem dBTm_immersion {p} (x: dB) (H : TmP p x)
: dB_of_Tm (Tm_of_dB x p H) = x.
Proof.
  unfold Tm_of_dB.
  unfold dB_of_Tm.
  rewrite TmcfTm_immersion.
  apply dBTmcf_immersion.
Qed.

Lemma TmP_dB_of_Tm {p} (x:Tm p) : TmP p (dB_of_Tm x).
Proof.
  apply TmPfromTmcf.
  apply contextFromTm.
Defined.

Theorem TmDB_immersion {p} (x:Tm p)
  : (x <-->* Tm_of_dB (dB_of_Tm x) p (TmP_dB_of_Tm x))%AK.
Proof.
  unfold Tm_of_dB.
  unfold dB_of_Tm.

  eapply rst_trans.
  { apply rst_sym.
    apply TmTmcf_immersion. }
  apply Tm_of_Tmcf_compatibility0.
  apply TmcfDB_immersion.
Qed.

Check dBTm_immersion.
Check TmDB_immersion.

Check TmcfsTms_immersion.
Check TmsTmscf_immersion.

Check Tms_of_Tmscf_compatibility0.