From Category Require Import Lib Theory Theory.Morphisms.
From Category.Instance Require Import  Sets Sets.Cartesian.
From CwFdeBruijn Require Import CatPsh Uwcwf MwM Structure.Uwcwf LambdaModels Lib.Transport.

Section MwM_Constructor.
    Context
  (* Data *)
    (T : Type)
    (S : Type)
    (S_id : S)
    (S_comp : S->S->S)
    (T_subst: T -> S -> T)
    (S_snoc : S -> T -> S)
    (S_π₁ : S -> S)
    (T_π₂ : S -> T)
  (* Compatibility *)
    {T_Setoid : Setoid T}
    {S_Setoid : Setoid S}
    (S_comp_proper : Proper (equiv ==> equiv ==> equiv) S_comp)
    (T_subst_proper : Proper (equiv ==> equiv ==> equiv) T_subst)
    (S_snoc_proper : Proper (equiv ==> equiv ==> equiv) S_snoc)
    (S_π₁_proper : Proper (equiv ==> equiv) S_π₁)
    (S_π₂_proper : Proper (equiv ==> equiv) T_π₂)
  (* Equations *)
    (idl : forall δ, S_comp S_id δ ≈ δ)
    (idr : forall δ, S_comp δ S_id ≈ δ)
    (ass : forall δ1 δ2 δ3,
      S_comp δ1 (S_comp δ2 δ3) ≈ S_comp (S_comp δ1 δ2) δ3)
    (subst_id : forall a, T_subst a S_id ≈ a)
    (subst_subst : forall a δ γ , T_subst a (S_comp γ δ) ≈ T_subst (T_subst a γ) δ)
    (snocomp : forall δ a γ, S_comp (S_snoc δ a) γ ≈ S_snoc (S_comp δ γ) (T_subst a γ))
    (π₁comp : forall γ δ, S_comp (S_π₁ γ) δ ≈ S_π₁ (S_comp γ δ))
    (π₂subst : forall γ δ, T_subst (T_π₂ γ) δ ≈ T_π₂ (S_comp γ δ))
    (snoceta : forall δ, S_snoc (S_π₁ δ) (T_π₂ δ) ≈ δ)
    (π₁snoc : forall δ a, S_π₁ (S_snoc δ a) ≈ δ)
    (π₂snoc : forall a δ, T_π₂ (S_snoc δ a) ≈ a).

  Local Definition T_SetoidObject := {|
    carrier := T;
    is_setoid := T_Setoid
  |}.

  Local Definition make_MwM_C : Category.
  Proof using S S_Setoid S_comp S_comp_proper S_id ass idl idr.
    unshelve refine (Build_Category'
      (fun (_ _ : Datatypes.unit) => S)
      (fun _ => S_id)
      (fun _ _ _ => S_comp)).
    - intros [] []; exact idl.
    - intros [] []; exact idr.
    - intros [] [] [] []; exact ass.
  Defined.

  Local Definition make_MwM_CwP : CwP.
  Proof using
      S S_Setoid S_comp S_comp_proper S_id T T_Setoid T_subst
      T_subst_proper ass idl idr subst_id subst_subst.
    refine(make_cwp make_MwM_C _).
    unshelve eapply Build_Functor.
    - exact (fun _ => T_SetoidObject).
    - intros [] [] δ.
      unshelve eapply Build_SetoidMorphism.
      { exact (fun x => T_subst x δ). }
      intros ? ? e.
      apply T_subst_proper; [exact e|reflexivity].
    - intros [] []. simpl.
      unfold SetoidMorphism_equiv.
      intros ? ? e ?.
      simpl. now rewrite e.
    - intros []. exact subst_id.
    - intros [] [] [] ? ? ?. apply subst_subst.
  Defined.

  Local Definition make_MwM_UWCwF : UWCwF.
  Proof using
    S S_Setoid S_comp S_comp_proper S_id S_snoc S_snoc_proper S_π₁ S_π₁_proper T_π₂ S_π₂_proper T T_Setoid T_subst T_subst_proper ass idl idr snoceta snocomp subst_id subst_subst π₁comp π₁snoc π₂snoc π₂subst.
  split with make_MwM_CwP.
  apply (@make_uwcwf make_MwM_CwP () (fun x=>x)).
  intros [].
  unshelve eapply Build_Isomorphism.
    + unshelve eapply Build_Transform'.
      * intros []; simpl.
        unshelve eapply Build_SetoidMorphism.
        --intros[δ x]. apply (S_snoc δ x).
        --intros [] [] [e1 e2]; simpl in *.
          apply S_snoc_proper; [exact e1| exact e2].
      * intros [] [] γ [δ x]. simpl in *. now rewrite snocomp.
    + unshelve eapply Build_Transform'.
      * intros []; simpl.
        unshelve eapply Build_SetoidMorphism.
        --intros δ. exact (S_π₁ δ, T_π₂ δ).
        --intros ? ? e; simpl in *; split; now rewrite e.
      * intros [] [] δ γ; simpl in *; split.
        -- now rewrite π₁comp.
        -- now rewrite π₂subst.
    + intros [] δ. simpl in *.
      now rewrite idr, snoceta.
    + intros [] [δ x]. simpl in *; split.
      * now rewrite idr, π₁snoc.
      * now rewrite subst_id,π₂snoc.
  Defined.

  Definition make_MwM : MwM.
  Proof using All.
    split with make_MwM_UWCwF.
    unshelve eapply Build_MonoidWithModule.
    intros []; reflexivity.
  Defined.

  Section λMwM_Constructor.
    Context
    (* Data *)
    (T_app : T -> T -> T)
    (T_lam : T -> T)
    (* Compatibility*)
    (T_app_proper : Proper (equiv ==> equiv ==> equiv) T_app)
    (T_lam_proper : Proper (equiv ==> equiv) T_lam)
    (* Equations *)
    (app_subst : forall a b δ, T_subst (T_app a b) δ ≈ T_app (T_subst a δ) (T_subst b δ) )
    (lam_subst : forall a δ, T_subst (T_lam a) δ ≈ T_lam (T_subst a (S_snoc (S_comp δ (S_π₁ S_id))(T_π₂ S_id))) ).

  Definition make_λMwM : λMwM.
  Proof using All.
    unshelve esplit; [split with make_MwM_UWCwF|].
    2: { exact (MwM_MonoidWithModule make_MwM). }
    simpl.
    apply make_isλmodel.
    - unshelve eapply Build_Transform'.
      + intros [].
        unshelve eapply Build_SetoidMorphism.
        { intros [a b].
          exact (T_app a b). }
        intros [? ?] [? ?] [e1 e2]; simpl in e1, e2.
        now rewrite e1, e2.
      + intros [] [] δ [a b]. simpl. apply app_subst.
    - unshelve eapply Build_Transform'.
      + intros [].
        apply (Build_SetoidMorphism _ _ _ _ T_lam).
        exact T_lam_proper.
      + intros [] [] δ a. apply lam_subst.
  Defined.

  End λMwM_Constructor.
End MwM_Constructor.

Section MwM_morphism_Constructor.
  Context { M N : MwM }
  (* Data *)
  (F_sbs : @MwM_S M -> @MwM_S N)
  (F_tm : @MwM_T M -> @MwM_T N)
  (* Compatibility *)
  (F_sbs_proper : Proper (equiv ==> equiv) F_sbs)
  (F_tm_proper : Proper (equiv ==> equiv) F_tm)
  (* Equations *)
  (F_id : F_sbs id ≈ id)
  (F_comp : forall δ1 δ2, F_sbs (δ1∘δ2) ≈ (F_sbs δ1)∘(F_sbs δ2))
  (F_subst : forall a δ, F_tm (a[δ]) ≈ (F_tm a) [F_sbs δ])
  (F_pi1 : forall δ, F_sbs (MwM_pi1 δ) ≈ MwM_pi1 (F_sbs δ))
  (F_pi2 : forall δ, F_tm (MwM_pi2 δ) ≈ MwM_pi2 (F_sbs δ))
  .

  Definition make_MwMmorphism : M ~{MwMs}~> N.
  Proof using
    F_comp F_id F_pi1 F_pi2 F_sbs F_sbs_proper F_subst F_tm F_tm_proper M N.
    unshelve esplit; [|exact tt]; unshelve esplit.
    - unshelve eapply make_cwpmorphism.
      + unshelve eapply Build_Functor.
        * unshelve eapply Build_SetoidMorphism.
          -- intro. exact (⋆_N).
          -- proper.
        * intros ? ? δ. simpl.
          exact (F_sbs (homcast (hasSingleContext _ _ _) (hasSingleContext _ _ _) δ)).
        * intros ? ? ? ? δ. now rewrite δ.
        * intros ?. simpl.
          rewrite homcast_id.
          apply F_id.
        * intros ? ? ? ? ?.
          simpl.
          erewrite homcast_comp.
          rewrite F_comp.
          reflexivity.
      + unshelve eapply Build_Transform'.
        * intros ?. simpl.
          unshelve eapply Build_SetoidMorphism.
          -- intro a. exact (F_tm (Logic.transport fobj[Tm] (hasSingleContext _ _ _) a)).
          --intros ? ? e. simpl.
            apply F_tm_proper.
            refine (proper_transport obj[`1 (M)] fobj[Tm] _ _ _ _ _ _ e).
        * intros ? ? δ a. simpl.
          etransitivity; [symmetry; apply F_subst|symmetry].
          f_equiv.
          erewrite (transport_subst _ _ δ a).
          reflexivity.
    - unshelve eapply make_uwcwfmorphism.
      + intros ?. simpl. symmetry. apply (hasSingleContext N _).
      + reflexivity.
      + intros ? ? δ. simpl.
        etransitivity.
        2:{ apply F_pi1. }
        f_equiv.
        unfold MwM_pi1, MwM_transport_to_exttgt.
        rewrite homcast_trans.
        simpl in *.
        erewrite <-(homcast_map (UIP := MwM_CtxUIP) (fun x y => π1 (m:=x) (n:=y)) δ).
        {reflexivity. }
        all: apply (hasSingleContext M _).
      + intros ? ? δ. simpl.
        etransitivity.
        2:{ apply F_pi2. }
        f_equiv.
        unfold MwM_pi2, MwM_transport_to_exttgt.
        rewrite homcast_trans.
        unshelve erewrite ((homcast_funfam _ (UIP := MwM_CtxUIP) (fun m n (δ:m ~> s n) => π2 δ)) δ).
        1,3: apply (hasSingleContext M _).
        reflexivity.
  Defined.

  Section λMwM_morphism_Constructor.
    Context {isλM : isλmodel M} {isλN : isλmodel N}.
    Let λM : λMwM := ((MwM_incl M;isλM); MwM_MonoidWithModule M).
    Let λN : λMwM := ((MwM_incl N;isλN); MwM_MonoidWithModule N).

    Context
      (F_app : forall a b : @MwM_T λM,
        F_tm (MwM_app a b) ≈ @MwM_app λN (F_tm a)( F_tm b))
      (F_lam : forall a : @MwM_T λM, F_tm (MwM_lam a) ≈ @MwM_lam λN (F_tm a)).

    Definition make_λMwMmorphism : λM ~{λMwMs}~> λN.
    Proof using All.
      unshelve esplit; unshelve esplit.
      - exact (`1 make_MwMmorphism).
      - simpl.
        apply make_λUWCwFmorphism.
        + simpl.
          induction m using MwM_ind.
          intros a b.
          rewrite (MwM_CtxUIP _ _).
          simpl.
          apply F_app.
        + simpl.
          induction m using MwM_ind.
          intros a.
          rewrite (MwM_CtxUIP _ _).
          simpl.
          etransitivity;[|apply F_lam].
          unfold MwM_lam.
          rewrite transport_trans.
          rewrite (MwM_CtxUIP _ _).
          reflexivity.
    Defined.


  End λMwM_morphism_Constructor.

End MwM_morphism_Constructor.
