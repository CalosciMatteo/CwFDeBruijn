From Category Require Import Theory Lib.
From Category.Instance Require Import Sets.
From Category Require Import Theory.Morphisms.
From Category Require Import Tactics2.
From CwFdeBruijn Require Import CatPsh Uwcwf.
From CwFdeBruijn.Structure Require Import Uwcwf.

Section lift.
  Context {C : UWCwF} {m n : C}.

  Definition lift_on_sbs (δ : m ~> n) : (s m ~> s n)
    := ⟨δ ∘[C] π1 id, π2 id⟩.

  Global Instance proper_lift : (Proper (equiv ==> equiv) lift_on_sbs).
  Proof.
    intros ? ? E.
    unfold lift_on_sbs. rewrite E. proper.
  Qed.

End lift.

Section lift_properties.
  Context {C : UWCwF}.

Section lift_inj.
  Lemma lift_inj {m : ctx C} (n : ctx C) (a : Tm m) : injective (@lift_on_sbs _ m n).
  Proof.
    apply Build_injective.
    intros δ γ E.
    assert (EE := proper_morphism {| morphism := π1; |} _ _ E).
    simpl in EE.
    unfold lift_on_sbs in EE.
    rewrite !pi1_snoc in EE.
    apply (π1id_epic a).
    exact EE.
  Qed.

  Lemma lift_inj_exttgt (m n : ctx C) : injective (@lift_on_sbs _ m (s n)).
  Proof.
    apply Build_injective.
    intros δ ? E.
    unshelve eapply (inj E).
    apply lift_inj.
    exact (π2 δ).
  Qed.

  Lemma lift_inj_extsrc (m n : ctx C) : injective (@lift_on_sbs _ (s m) n).
  Proof.
    apply Build_injective.
    intros δ ? E.
    unshelve eapply (inj E).
    apply lift_inj.
    apply (π2 id).
  Qed.
End lift_inj.

Lemma lift_id (m:ctx C) : lift_on_sbs id[m] ≈ id[s m].
Proof.
  unfold lift_on_sbs.
  proper.
  symmetry.
  apply snoc_eta.
Qed.

Lemma lift_comp {m1 m2 m3:ctx C} (γ : m1~>m2) (δ : m2~>m3)  : lift_on_sbs (δ∘γ) ≈ (lift_on_sbs δ) ∘ (lift_on_sbs γ).
Proof.
  unfold lift_on_sbs.
  rewrite snoc_comp.

  proper. rewrite pi1_comp, pi2_subst.
  proper. rewrite pi1_snoc, pi2_snoc.
  reflexivity.
Qed.

End lift_properties.

Section lift_as_CwPmorphism.
  Context {C:UWCwF}.

  Definition Lift : CwP_Morphism C C.
  Proof.
    unshelve eapply make_cwpmorphism.
    - unshelve eapply Build_Functor.
      + intro m. exact (s m).
      + intros m n δ. simpl. exact (lift_on_sbs δ).
      + intros m n. apply proper_lift.
      + apply lift_id.
      + intros ? ? ? ? ?. apply lift_comp.
    - simpl.
      unshelve eapply Build_Transform'.
      + intros m.
        unshelve eapply Build_SetoidMorphism.
        * intro a.
          exact (subst a (π1 id)).
        * intros ? ? e. now rewrite e.
      + intros m n δ a. simpl.
        fold (subst (a [π1 id{C}]) (lift_on_sbs δ)).
        fold (subst a δ).
        rewrite !substsubst.
        f_equiv.
        rewrite pi1_comp.
        rewrite id_left.
        unfold lift_on_sbs.
        rewrite pi1_snoc.
        reflexivity.
  Defined.     
End lift_as_CwPmorphism.
