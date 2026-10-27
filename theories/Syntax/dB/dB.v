From CwFdeBruijn.Syntax.Setup Require Export Setup.
From Stdlib Require Export Bool.

Set Boolean Equality Schemes.
Set Decidable Equality Schemes.

Inductive dB : Type :=
  | dB_ref (i : nat)
  | dB_app (x y : dB) : dB
  | dB_lam (x : dB) : dB.

Unset Boolean Equality Schemes.
Unset Decidable Equality Schemes.

Definition slide (f : nat -> nat) (i : nat) : nat :=
  match i with 0 => 0 | S j => S (f j) end.

Fixpoint reindex (f : nat -> nat) (x : dB) {struct x} : dB :=
  match x with
  | dB_ref i => dB_ref (f i)
  | dB_app x y => dB_app (reindex f x) (reindex f y)
  | dB_lam x => dB_lam (reindex (slide f) x)
  end.

Definition lift (f : nat -> dB) (i : nat) : dB :=
  match i with 0 => dB_ref 0 | S j => reindex S (f j) end.

Fixpoint dB_subst (f : nat -> dB) (x : dB) {struct x} : dB :=
  match x with
  | dB_ref i => f i
  | dB_app x y => dB_app (dB_subst f x) (dB_subst f y)
  | dB_lam x => dB_lam (dB_subst (lift f) x)
  end.

Definition dB_snoc (δ : nat -> dB) (x : dB) (i : nat) : dB :=
  match i with
  | 0 => x
  | S i' => δ i'
  end.

(* Composition of substitution *)
Definition assign_comp (δ₁ δ₂ : nat -> dB) (i : nat) : dB :=
  dB_subst δ₂ (δ₁ i).

Definition assign_π₁ (δ : nat -> dB) i : dB := δ (S i).

Lemma dB_eq_spec (x y : dB) : reflect (x = y) (dB_beq x y).
Proof.
  apply iff_reflect.
  split.
  - apply internal_dB_dec_lb.
  - apply internal_dB_dec_bl.
Qed.