From Stdlib Require Import Nat PeanoNat Lia.
From Category Require Import Theory Lib.
From Category.Instance Require Import
  Sets.
From CwFdeBruijn Require Import CatPsh Uwcwf Structure.Uwcwf Structure.Uwcwf.Transport.
From CwFdeBruijn Require Import 
  Contextual
  Construction.FlippedComprehension
  Structure.FlippedComprehension
  Structure.FlippedComprehension.IterUpshift
  Structure.FlippedComprehension.IterTmUpshift.


Section Iter_Snoc.

Context {C : UWCwFN}.

Lemma iter_upshift_Eq_snoc {m n itism itisn : C} (i:nat)
  (Em : iter i s m = itism)
  (En : iter i s n = itisn)
  (Ens : iter i s (s n) = s itisn)  
  (δ : m ~> n) (a : Tm m)
  : iter_upshift_Eq i Em Ens ⟨δ,a⟩ ≈ ⟨iter_upshift_Eq i Em En δ, iter_Tm_upshift_Eq i Em a⟩.
Proof.
  revert m n itism itisn Em En Ens δ a;
   induction i;
   intros m n itism itisn Em En Ens δ a.
  - simpl in *.
    destruct Em, En.
    rewrite !iter_upshift_Eq_beta_0, iter_Tm_upshift_Eq_beta_0.
    reflexivity.
  - simpl in *.
    simpl.
    destruct Em, En.
    erewrite !iter_upshift_Eq_beta_S, iter_Tm_upshift_Eq_beta_S.
    simpl; unfold Up_tm_ntr_data.
    rewrite <-upshift_snoc.
    f_equiv.
    apply IHi.
    Unshelve.
    all: try reflexivity; apply Nat.iter_swap.
Qed.

Lemma iter_upshift_snoc {m n : C} (i:nat)
  (δ : m ~> n) (a : Tm m)
  : Logic.transport _ (Nat.iter_swap _ _ _ _) (iter_upshift i ⟨δ,a⟩) ≈ ⟨(iter_upshift i δ) , (iter_Tm_upshift i a)⟩.
Proof.
  apply (iter_upshift_Eq_snoc i eq_refl eq_refl _).
Qed.

End Iter_Snoc.