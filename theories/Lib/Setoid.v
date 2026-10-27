From Category Require Import Lib Theory.

Lemma eq_to_equiv {A} `{Setoid A} (x y : A) (p:x = y): x ≈ y.
Proof.
  destruct p.
  reflexivity.
Qed.