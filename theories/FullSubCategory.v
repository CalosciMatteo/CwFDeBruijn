From Category Require Import Lib Theory.
From Category Require Import Construction.Subcategory.

Section Subcategory.
  Context {C : Category} (S : Subcategory C).

  Definition Incl_Pred (X : obj[Sub C S]) : sobj C S (Incl _ _ X)
    := `2 X.

End Subcategory.

Section FullSubCategory.
Context (C:Category) (sobj: C -> Type).

Program Definition make_FullSubCategory : Subcategory C
:= {|
  Subcategory.sobj := sobj;
  Subcategory.shom := fun _ _ _ _ _ => Datatypes.unit
|}.

Lemma FullSubCategory_Full : Full _ make_FullSubCategory.
Proof.
  unfold Full, make_FullSubCategory, shom. simpl. intros. exact tt.
Qed.
End FullSubCategory.