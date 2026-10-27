From Stdlib Require Export Relations.
From Stdlib Require Import Classes.RelationClasses.

Lemma rt_refl_propositional {X} {R: relation X} {x x' : X}
  (e : x = x')
  : clos_refl_trans X R x x'.
Proof.
  subst.
  apply rt_refl.
Qed.

Lemma rst_refl_propositional {X} {R: relation X} {x x' : X}
  (e : x = x')
  : clos_refl_sym_trans X R x x'.
Proof.
  subst.
  apply rst_refl.
Qed.

Lemma rt_compatibility {X} (R: relation X) {Y}
  (S : relation Y) (f : X -> Y)
  (H :forall x y, R x y -> (clos_refl_trans _ S) (f x) (f y))
  (x y: X): (clos_refl_trans _ R x y) -> (clos_refl_trans _ S) (f x) (f y).
Proof.
  intro K.
  induction K.
  - apply H.
    exact H0.
  - apply rt_refl.
  - eapply rt_trans.
    + apply IHK1.
    + apply IHK2.
Qed.

Lemma rst_compatibility {X} (R: relation X) {Y}
  (S : relation Y) (f : X -> Y)
  (H :forall x y, R x y -> (clos_refl_sym_trans _ S) (f x) (f y))
  (x y: X): (clos_refl_sym_trans _ R x y) -> (clos_refl_sym_trans _ S) (f x) (f y).
Proof.
  auto with sets.
  intro K.
  induction K.
  - apply H.
    exact H0.
  - apply rst_refl.
  - apply rst_sym.
    exact IHK.
  - eapply rst_trans.
    + apply IHK1.
    + apply IHK2.
Qed.

(* Relating Equivalence [Classes.RelationClasses] and equivalence [Relations] *)

Theorem eqIffEq (A : Type) (R: relation A) : Equivalence R <-> equivalence A R.
Proof.
  split.
  - intros [? ?].
    apply Build_equivalence; assumption.
  - intros [? ?].
    apply Build_Equivalence; assumption.
Defined.