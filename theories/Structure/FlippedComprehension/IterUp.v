From Stdlib Require Import Nat PeanoNat.
From Category Require Import Theory Lib.
From Category.Instance Require Import
  Sets.
From CwFdeBruijn Require Import 
  Lib.Transport Lib.Setoid
  CatPsh Uwcwf Structure.Uwcwf Structure.Uwcwf.Transport.
From CwFdeBruijn Require Import 
  Contextual
  Construction.FlippedComprehension
  Structure.FlippedComprehension
  Structure.FlippedComprehension.IterUpshift
  Structure.FlippedComprehension.IterTmUpshift
.

Section Iter_Up.

Context {C:UWCwFN}.

Definition iter_Up (n:nat) : C~{CwPs}~>C
  := (iter n (λ x, Up∘x) id{CwPs}).

Lemma fctx_iter_Up {m:C} i 
  : fctx[ iter_Up i ] m = iter i s m.
Proof.
  induction i.
  - reflexivity.
  - refine (f_equal s IHi).
Qed.

Lemma fsbs_iter_Up {m n:C} (δ : m ~>n) (i :nat)
  Em En
  : fsbs[iter_Up i] δ ≈
    iter_upshift_Eq i Em En δ.
Proof.
  induction i.
  - rewrite iter_upshift_Eq_beta_0.
    reflexivity.
  - etransitivity.
    2:{ 
      apply eq_to_equiv. symmetry.
      eapply (iter_upshift_Eq_beta_S i _ _ _ _ δ). }
    simpl.
    f_equiv.
    apply IHi.
    Unshelve.
    all: symmetry; apply fctx_iter_Up.
Qed.

Lemma fsbs_iter_Up_fixedargs {m n:C} (δ : m ~>n) (i :nat)
  : fsbs[iter_Up i] δ ≈
    iter_upshift_Eq i (eq_sym (fctx_iter_Up _)) (eq_sym (fctx_iter_Up _)) δ.
Proof.
  apply fsbs_iter_Up.
Qed.

Lemma ftm_iter_Up {m :C} (a :Tm m) (i :nat)
  E
  : ftm[iter_Up i] a ≈
    iter_Tm_upshift_Eq i E a.
Proof.
  induction i.
  - rewrite iter_Tm_upshift_Eq_beta_0.
    reflexivity.
  - etransitivity.
    2:{ 
      apply eq_to_equiv. symmetry.
      eapply (iter_Tm_upshift_Eq_beta_S i _ _ a). }
    simpl.
    f_equiv.
    apply IHi.
    Unshelve.
    all: symmetry; apply fctx_iter_Up.
Qed.

Lemma ftm_iter_Up_fixedargs {m:C} (a :Tm m) (i :nat)
  : ftm[iter_Up i] a ≈
    iter_Tm_upshift_Eq i (eq_sym (fctx_iter_Up _)) a.
Proof.
  apply ftm_iter_Up.
Qed.

Lemma ctx_to_iter_Up (m:C)
  : m = fctx[iter_Up (nnp_l m)] (⋆__).
Proof. 
  induction m using UWCwFN_ind.
  - rewrite nnp_l_distobj.
    reflexivity.
  - rewrite nnp_l_s.
    apply (f_equal s IHm).
Qed.
End Iter_Up.