From Stdlib Require Import Nat PeanoNat Lia EqdepFacts.

From Category Require Import Lib Theory.
From Category.Theory Require Import Morphisms.
From Category.Construction Require Import Opposite.
From Category.Functor Require Import Product Hom Opposite.
From Category.Instance Require Import
  Sets Sets.Cartesian
  Fun Fun.Cartesian.

From CwFdeBruijn Require Import
  Lib.Transport
  Lib.Setoid

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
  Structure.FlippedComprehension.IterUpshiftSnoc

  Construction.Monoidification.CtxCmp.


(* The Projection morphism U from a UWCWFN to its monoidification *)

Section Projection_Morphism_U.
Context (C : UWCwFN).

Section CwP_Morphism.

Program Definition Mndf_U_ctx_fnc : C ⟶ Mndf_MwM C := {|
  fobj := λ Γ, ⋆_(Mndf_MwM C);
  fmap := λ _ _ δ, Build_Mndf_S_carrier δ
|}.
Next Obligation.
  proper; apply make_Mndf_S_rel_samectx; assumption.
Qed.
Next Obligation. apply Mndf_S_id_rew_0. Qed.
Final Obligation.
  change Mndf_S_rel with (@equiv _ (@Mndf_S_Setoid C)).
  symmetry.
  apply Mndf_S_compose_matching_ctx.
Qed.

Program Definition Mndf_U_tm_ntr
  : (@Tm C)  ⟹ (@Tm (Mndf_MwM C)) ◯ (Opposite.Opposite_Functor Mndf_U_ctx_fnc)
  := Build_Transform' 
      (λ Γ, {|morphism := Build_Mndf_T_carrier |}
        : fobj[@Tm C] Γ  ~{ Sets }~> fobj[(@Tm (Mndf_MwM C)) ◯ (Opposite.Opposite_Functor Mndf_U_ctx_fnc)] Γ)
      _.
Next Obligation.
  intros ? ? E.
  apply make_Mndf_T_rel_samectx.
  assumption.
Qed.
Final Obligation.
  revert x y f x0; intros n m δ a.
  apply Mndf_T_subst_matching_ctx.
Qed.

Definition Mndf_U_CwP_Morphism : C ~{CwPs}~> (Mndf_MwM C) := {|
    ctx_fnc := Mndf_U_ctx_fnc ;
    tm_ntr := Mndf_U_tm_ntr
  |}.

Lemma Mndf_U_CwP_Morphism_epic
  {D : obj[CwPs]}
  {F G : Mndf_MwM C ~{ CwPs }~> D}
  (H : F ∘ Mndf_U_CwP_Morphism ≈ G ∘ Mndf_U_CwP_Morphism)
  (UIP : forall Γ : C, (`1`1 H) (⋆_C) = (`1`1 H) Γ)
  : F ≈ G.
Proof.
  destruct H as [E_fnc E_tm].
  assert (E_sbs := (Functor_StrictEq_eq_on_sbs E_fnc)).
  destruct E_fnc as [E_ctx n].
  simpl in *; clear n.

  unshelve eapply make_CwP_Morphism_equiv.
  - intros [].
    apply (E_ctx (⋆_C)).
  - intros [] [] δ.
    etransitivity;[|apply (E_sbs _ _ (Mndf_S_rep δ))].
    simpl.
    
    assert (H:= E_sbs _ _ (Mndf_S_rep δ)).
    cbn in H.
    apply eq_to_equiv.
    apply homcast_rew.
    all : apply UIP.
  - intros [] a.
    etransitivity;[|apply (E_tm _ (Mndf_T_rep a))].
    simpl.
    f_equiv.
    apply UIP.
Qed.

Lemma Mndf_U_CwP_Morphism_epic_assumingUIP
  (UIP : forall D : CwP, UIP_ (obj[D]))
  : Epic Mndf_U_CwP_Morphism.
Proof.
  constructor.
  intros D F G H.
  unshelve eapply Mndf_U_CwP_Morphism_epic.
  { apply H. }
  intros. apply UIP.
Qed.

End CwP_Morphism.

Section UWCwF_Morphism.

Definition Mndf_U_UWCwF_Morphism : @UWCwF_Morphism C (Mndf_MwM C) (Mndf_U_CwP_Morphism).
Proof.
  unshelve eapply make_uwcwfmorphism.
  - reflexivity.
  - reflexivity.
  - cbn -[equiv].
    symmetry.
    apply Mndf_π1_carrier.
  - cbn -[equiv].
    symmetry.
    apply Mndf_π2_carrier.
Defined.

End UWCwF_Morphism.

End Projection_Morphism_U.