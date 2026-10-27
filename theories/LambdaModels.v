
From Category Require Import Lib Theory.
From Category.Theory Require Import Natural.Transformation.
From Category.Structure Require Import Cartesian.
From Category.Functor Require Import Product Hom Opposite.
From Category.Instance Require Import 
  Sets Sets.Cartesian Fun Fun.Cartesian.
From Category.Construction  Require Import Subcategory.
From CwFdeBruijn Require Import 
  Lib.Transport
  CatPsh Uwcwf Structure.Uwcwf
  Structure.Uwcwf.Lift
  MwM Contextual
  FullSubCategory.
 
Section definitions.

  Context {C : UWCwF}.

  Class isλmodel : Type := make_isλmodel
  { 
    app : (Tm × Tm) ⟹ @Tm C;
    lam : Tm ◯ (ctx_fnc (@Lift C))^op ⟹ Tm
  }.

End definitions.
Arguments isλmodel _ : clear implicits.

Section CategoriesOfModels.
  (* λ UWCwF *)
  Definition λUWCwF := { C : UWCwF & isλmodel C}.
  Definition λUWCwF_incl : λUWCwF -> UWCwF
    := @projT1 UWCwF (@isλmodel).

  Coercion λUWCwF_incl : λUWCwF >-> UWCwF.
  #[global]
  Instance λUWCwF_isλmodel (C : λUWCwF) : @isλmodel C
    := projT2 C.

  Record λUWCwF_Morphism {C D : λUWCwF} (F: λUWCwF_incl C ~{UWCwFs}~> λUWCwF_incl D) := make_λUWCwFmorphism {
    app_preserved : forall m (a b : fobj[Tm] m),
      ftm[`1 F] (app _ (a,b)) ≈ app _ (ftm[`1 F] a, ftm[`1 F] b);
    lam_preserved : forall m (a : fobj[Tm] (s m)),
      ftm[`1 F] (lam m a) ≈ lam (C:=D) _ (Logic.transport fobj[Tm] (ctxext_preserved (`2 F) m) (ftm[`1 F] a))
  }.

  Program Definition λUWCwF_Morphism_id (C:λUWCwF) :
    @λUWCwF_Morphism C C id[λUWCwF_incl C : obj[UWCwFs]] 
  := {|
      app_preserved := _;
      lam_preserved := _;
  |}.

  Lemma λUWCwF_Morphism_compose {B C D : λUWCwF}
  {G: λUWCwF_incl C ~{UWCwFs}~> λUWCwF_incl D}
  {F: λUWCwF_incl B ~{UWCwFs}~> λUWCwF_incl C}
  (Gis : λUWCwF_Morphism G)
  (Fis : λUWCwF_Morphism F) :
  λUWCwF_Morphism (G ∘ F).
  Proof.
    unshelve eapply make_λUWCwFmorphism.
    - intros n ? ?.
      cbn.
      rewrite (app_preserved F Fis n a b).
      rewrite (app_preserved G Gis).
      reflexivity.
    - intros.
      simpl.
      rewrite (lam_preserved F Fis).
      rewrite (lam_preserved G Gis).
      rewrite <- (transport_funfam (fun x => (transform[@tm_ntr _ _ (`1 G)] x))).
      simpl.
      rewrite (transport_f_equal _ _ fobj[Tm] (fctx[ `1 (G)])).
      rewrite transport_trans.
      reflexivity.
  Qed.

  Program Definition λUWCwFs_Sub_CwPs : Subcategory UWCwFs := {|
    sobj := @isλmodel;
    shom := λ C D Cis Dis F, @λUWCwF_Morphism (C; Cis) (D; Dis) F;

    scomp := λ _ _ _ _ _ _ _ _ Fis Gis, λUWCwF_Morphism_compose Fis Gis;
    sid := λ _ _, λUWCwF_Morphism_id _
  |}.
  

  Definition λUWCwFs := Sub UWCwFs λUWCwFs_Sub_CwPs.

  (* λ MwM *)
  Definition λMwM := { C : λUWCwFs & @MonoidWithModule (λUWCwF_incl C) }.
  Definition λMwM_incl : λMwM -> λUWCwF
    := @projT1 λUWCwFs (fun C =>  @MonoidWithModule (λUWCwF_incl C)).
  Definition λMwM_MwM_incl (M : λMwM) : MwM := (`1 `1 M ; `2 M).

  Coercion λMwM_MwM_incl : λMwM >-> MwM.
  Coercion λMwM_incl : λMwM >-> λUWCwF.
  #[global]
  Instance λMwM_MonoidWithModule (C : λMwM) : @MonoidWithModule C
    := projT2 (C).
  #[global]
  Instance λMwM_isλmodel (C : λMwM) : @isλmodel C
    := projT2 (`1 C).


  Definition λMwMs : Category := Sub _ (make_FullSubCategory λUWCwFs (MonoidWithModule ∘ λUWCwF_incl)%prg).

  (* λ cUWCwF *)
  Definition λcUWCwF := { C : λUWCwF & @PreContextual (λUWCwF_incl C) }.
  Definition λcUWCwF_incl : λcUWCwF -> λUWCwF
    := @projT1 λUWCwF (@PreContextual∘λUWCwF_incl)%prg.
  Definition λcUWCwF_cUWCwF_incl (C : λcUWCwF) : cUWCwF := (`1 `1 C; `2 C).

  Coercion λcUWCwF_incl : λcUWCwF >-> λUWCwF.
  Coercion λcUWCwF_cUWCwF_incl : λcUWCwF >-> cUWCwF.
  #[global]
  Instance λcUWCwF_PreContextual (C : λcUWCwF) : @PreContextual C
    := projT2 (C).
  #[global]
  Instance λcUWCwF_isλmodel (C : λcUWCwF) : @isλmodel C
    := projT2 (`1 C).

  (* λ UWCwFN *)
  Definition λUWCwFN := { C : λUWCwF & @NaturalNumberProperty (λUWCwF_incl C) }.
  Definition λUWCwFN_incl : λUWCwFN -> λUWCwF
    := @projT1 λUWCwF (@NaturalNumberProperty∘λUWCwF_incl)%prg.
  Definition λUWCwFN_cUWCwF_incl (C : λUWCwFN) : UWCwFN := (`1 `1 C; `2 C).

  Coercion λUWCwFN_incl : λUWCwFN >-> λUWCwF.
  Coercion λUWCwFN_cUWCwF_incl : λUWCwFN >-> UWCwFN.
  #[global]
  Instance λUWCwFN_Contextual (C : λUWCwFN) : @NaturalNumberProperty C
    := projT2 (C).
  #[global]
  Instance λUWCwFN_isλmodel (C : λUWCwFN) : @isλmodel C
    := projT2 (`1 C).

  Definition λUWCwFNs : Category := Sub _ (make_FullSubCategory UWCwFNs (isλmodel ∘ UWCwFN_incl)%prg).

End CategoriesOfModels.

Section Accessors.
  Context {M:λMwM}.

  Definition MwM_app (a:MwM_T) (b : MwM_T) : @MwM_T M := app _  (a,b).
  #[global] Instance proper_MwM_app
    : (Proper (equiv ==> equiv ==> equiv) (MwM_app)).
  Proof.
    intros ? ? Ea ? ? Eδ.
    unfold MwM_app.
    now rewrite Eδ, Ea.
  Qed.

  Definition MwM_upeq := (eq_sym (hasSingleContext M _ (s(⋆_ _)))).

  Definition MwM_lam (a:MwM_T) : @MwM_T M := lam _ (Logic.transport fobj[Tm] MwM_upeq a).
  #[global] Instance proper_MwM_lam
    : (Proper (equiv ==> equiv) MwM_lam).
  Proof.
    intros ? ? Ea.
    unfold MwM_lam.
    simpl.
    now rewrite (proper_transport obj[M] fobj[Tm] _ _ _ _ _ _ Ea).
  Qed.
End Accessors.