From Stdlib Require Import Nat PeanoNat Arith Lia.

From Category Require Import Lib Theory.
From Category.Instance Require Import Sets Fun Sets.Cartesian Fun.Cartesian.
From Category.Functor Require Import Hom.
From Category.Construction Require Import Opposite.

From CwFdeBruijn Require Import
  CatPsh Uwcwf
  Contextual
  Construction.FlippedComprehension
  Construction.Monoidification.SubstRel
  Construction.Monoidification.Compose
  Construction.Monoidification.TmRel
  Construction.Monoidification.Substitution
  Structure.FlippedComprehension
  Structure.FlippedComprehension.IterUpshift.

Section Monoidification.

Context {C : UWCwFN}.

Definition Mndf_S_category : Category := {|
  obj := Datatypes.unit;
  hom     := fun x y => @Mndf_S_carrier C; 
  id      := fun x => Mndf_S_id;
  compose := fun x y z f g  => Mndf_S_compose f g;
  id_left := fun x y f => Mndf_S_compose_id_left f;
  id_right := fun x y f => Mndf_S_compose_id_right f;
  comp_assoc := fun _ _ _ _ f g h => Mndf_S_compose_assoc f g h;
  comp_assoc_sym := fun _ _ _ _ f g h => symmetry (Mndf_S_compose_assoc f g h)
|}.

Program Definition Mndf_Tm : [(Mndf_S_category ^op), Sets] := {|
  fobj := λ _, @Mndf_T_SetoidObject C;
  fmap := λ _ _ δ, Mndf_T_subst_SetoidMorphism δ;
  fmap_id := λ _, Mndf_T_subst_id;
  fmap_comp := λ _ _ _ γ δ, λ a,  Mndf_T_subst_assoc a δ γ; 
|}.

Final Obligation.
proper.
apply Mndf_T_subst_respects.
- reflexivity.
- assumption.
Qed.

Definition Mndf_CwP := {|
  ctx := Mndf_S_category;
  Tm := Mndf_Tm
|}.

End Monoidification.

Arguments Mndf_CwP _ : clear implicits.