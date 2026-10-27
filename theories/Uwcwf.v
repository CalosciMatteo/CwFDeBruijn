From Category Require Import Lib Lib.Tactics2 Theory.
From Category.Functor Require Import Hom Opposite.
From Category.Instance Require Import
  Sets Sets.Cartesian Fun Fun.Cartesian.
From Category.Structure Require Import Cartesian.
From Category.Construction Require Import Subcategory.

Require Import Equations.Prop.Logic.

From CwFdeBruijn Require Import CatPsh.

(*
  This file introduce the category of
    unityped weak category with families
  
  An uwcwf is
  - a category Ctx of contexts
  - with a distinguished object ⋆
  - a presheaf Tm : C^op ⟶ Set
  - a context comprehension operation:
    - for each context n there is a context s n
    - a natural (in m) isomorphism Hom(m,n)×Tm(m)≃Hom(m,s(n))
      we call its components:
      - cons ("⟨,⟩")
      - π1
      - π2 

  A (strict) morphism of uwcwf is
  - a functor F : C ⟶ D between the underlying categories
  - a nat transf σ : Tm C ⟹ (Tm D) ∘ F
  - σ preserv context comprehension on the nose:
    - F(⋆) = ⋆
    - F(s n) = s (F n)
    - F(π1 δ) = π1 (F δ)
    - σ _ (π2 δ) = π2 (F δ)
    - F <δ, a> = <F δ, σ _ a>
*)

Declare Scope CwF_scope.
Delimit Scope CwF_scope with CwF.
Open Scope CwF_scope.

Section definitions.
  Context {C : CwP}.

  Class UnitypedWeakCwF : Type := make_uwcwf {
  distobj : C ;
  
  ctxext : C -> C;
  ctxcmp : forall (n : C),
    [Hom ─ , n ] × Tm ≅[Fun.Fun] [Hom ─ , ctxext n ]
}.
End definitions.

Definition UWCwF := { C : CwP & @UnitypedWeakCwF C}.
Definition UWCwF_incl : UWCwF -> CwP
  := @projT1 CwP (@UnitypedWeakCwF).
Coercion UWCwF_incl : UWCwF >-> CwP.
Instance UWCwF_UnitypedWeakCwF (C : UWCwF) : @UnitypedWeakCwF C
  := projT2 C.

Notation "⋆_ C" := (@distobj C) (at level 75) : CwF_scope.

Definition s {C : UWCwF} (n : ctx C) : ctx C
  := ctxext n.
#[global]
Instance s_proper {C : UWCwF} {m n:C} : (Proper (eq ==> eq) (@s C)).
Proof.
  intros ? ? E.
  unfold s.
  now rewrite E.
Qed.

Lemma ctxext_to_s {C : UWCwF} : ctxext = @s C.
Proof.
  reflexivity.
Qed.

Definition snoc {C : UWCwF} {m n : C}
  (δ : m ~{C}~> n) (a : Tm m)
  : m ~{C}~> s n
  := (to (ctxcmp _) _ (δ,a)).
Notation "'⟨' δ ',' a '⟩'" := (snoc δ a) (δ at level 40, a at level 40) : CwF_scope.

#[global] Instance proper_snoc {C : UWCwF} {m n : C}
  : (Proper (equiv ==> equiv ==> equiv) (@snoc _ m n)).
Proof.
  intros ? ? Eδ ? ? Ea.
  unfold snoc.
  now rewrite Eδ, Ea.
Qed.

Definition π1 {C : UWCwF} {m n : C} (δ : m ~{C}~> s n)
  : m ~{C}~> n
  := exl (C:=Sets) ((ctxcmp _)⁻¹ _ δ).
#[global] Instance proper_π1 {C : UWCwF} {m n:C} : (Proper (equiv ==> equiv) (@π1 _ m n)).
Proof.
  intros ? ? E.
  unfold π1.
  now rewrite E.
Qed.
Definition π2 {C : UWCwF} {m n : C} (δ : m ~{C}~> s n)
  : Tm m
  := exr (C:=Sets) ((ctxcmp _)⁻¹ _ δ).
#[global] Instance proper_π2 {C : UWCwF} {m n:C} : (Proper (equiv ==> equiv) (@π2 _ m n)).
Proof.
  intros ? ? E.
  unfold π2.
  now rewrite E.
Qed.

Ltac unfold_uwcwf_notation := unfold π1, π2, subst.

Section UWCwF_DefProperties.
Context (C : UWCwF).

(* Functoriality of Tm gives *)
Lemma substsubst {m' m n : C} (a: Tm n) (δ : m ~{C}~> n) (γ : m' ~> m)
  : a[δ][γ] ≈ a[δ ∘ γ].
Proof.
  symmetry.
  apply ((fmap_comp (Functor:= Tm)) γ δ a).
Qed.
(* Naturality of context comprehension gives: *)
Lemma pi1_comp {l m n : C} (γ : l ~> m) (δ : m ~> s n)
  : (π1 δ) ∘ γ ≈ π1 (δ ∘ γ).
Proof. apply (naturality (from (ctxcmp n)) _ _ γ δ). Qed.

Lemma pi2_subst {l m n : C} (γ : l ~> m) (δ : m ~> s n)
  : (π2 δ)[γ] ≈ π2 (δ ∘ γ).
Proof. apply (naturality (from (ctxcmp n)) _ _ γ δ). Qed.

Lemma snoc_comp {l m n : C} (γ : l ~> m) (δ : m ~> n) (a : Tm m)
  : ⟨ δ , a ⟩ ∘[C] γ ≈ ⟨ δ ∘ γ , a[γ] ⟩.
Proof. apply (naturality (to (ctxcmp n)) _ _ γ (δ,a)). Qed.

(* Since context comprehension is an isomorphism we have: *)
Lemma pi1_snoc {m n : C} (δ : m ~> n) (a : Tm m)
  : π1⟨ δ , a ⟩ ≈ δ.
Proof.
  unfold_uwcwf_notation.
  rewrite ((iso_from_to (ctxcmp n) m (δ,a))
    : (ctxcmp n)⁻¹ m ⟨ δ, a ⟩ ≈ _).
  cat_simpl.
Qed.

Lemma pi2_snoc {m n : C} (δ : m ~> n) (a : Tm m)
  : π2⟨ δ , a ⟩ ≈ a.
Proof.
  unfold_uwcwf_notation.
  rewrite ((iso_from_to (ctxcmp n) m (δ,a))
  : (ctxcmp n)⁻¹ m ⟨ δ, a ⟩ ≈ _).
  apply ((@fmap_id _ _ Tm _) a).
Qed.

Lemma snoc_eta {m n : C} (δ : m ~> s n)
  : δ ≈ ⟨π1 δ,π2 δ⟩.
Proof.
  spose (iso_to_from (ctxcmp n) m δ) as X.
  rewrite (surjective_pairing ((ctxcmp n)⁻¹ m δ)) in X.
  revert X.
  cat.
Qed.

End UWCwF_DefProperties.
Arguments snoc_eta {_ _ _ }.
Arguments snoc_comp {_ _ _ _}.
Record UWCwF_Morphism {C D : UWCwF} (F: CwP_Morphism C D) := make_uwcwfmorphism {

  distobj_preserved : fctx[ F ] (⋆_C) = ⋆_D;
  ctxext_preserved : forall n, fctx[ F ] (s n) = s (fctx[ F ] n);
    (* Rocq equality, since we require preservation on the nose*)
  
  pi1_preserved : forall m n (δ : m ~> s n),
    fsbs[F] (π1 δ) ≈
    π1 (transport (fun x => fctx[F] m ~{ D }~> x) (ctxext_preserved n)
      (fsbs[F] δ));

  pi2_preserved : forall m n (δ : m ~> s n),
    ftm[ F ] (π2 δ) ≈ 
    π2 (transport (fun x => fctx[F] m ~{ D }~> x) (ctxext_preserved n)
      (fsbs[F] δ))
}.
Arguments distobj_preserved {_ _ _} _.
Arguments ctxext_preserved {_ _ _} _ _.

Program Definition UWCwF_Morphism_id (C:UWCwF) :
  @UWCwF_Morphism C C CwP_Morphism_id := {|
  ctxext_preserved := fun n => eq_refl
|}.

Lemma UWCwF_Morphism_compose {B C D : UWCwF}
  {G : CwP_Morphism C D}
  {F : CwP_Morphism B C}
  (Gis : UWCwF_Morphism G)
  (Fis : UWCwF_Morphism F) :
  UWCwF_Morphism (CwP_Morphism_compose G F).
Proof.
  unshelve eapply make_uwcwfmorphism.
  - intro n.
    exact (eq_trans
      (f_equal fctx[ G] (ctxext_preserved Fis n))
      (ctxext_preserved Gis (fctx[ F] n))).
  - intros.
    simpl.
    rewrite (distobj_preserved Fis).
    rewrite (distobj_preserved Gis).
    reflexivity.
  - intros; simpl.
    rewrite 2 pi1_preserved.
    now rewrite transport_functorial_cod, transport_trans.
  - intros; simpl.
    rewrite 2 pi2_preserved.
    now rewrite transport_functorial_cod, transport_trans.
Defined.

Program Definition UWCwFs_Sub_CwPs : Subcategory CwPs := {|
  sobj := @UnitypedWeakCwF;
  shom := λ C D Cis Dis F, @UWCwF_Morphism (C; Cis) (D; Dis) F;

  scomp := λ _ _ _ _ _ _ _ _ Fis Gis, UWCwF_Morphism_compose Fis Gis;
  sid := λ _ _, UWCwF_Morphism_id _
|}.

Definition UWCwFs := Sub CwPs UWCwFs_Sub_CwPs.