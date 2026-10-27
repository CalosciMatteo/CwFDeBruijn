From Category Require Import Lib Theory.

  #[global] Instance proper_iter {A:Type} {i:nat} {isA :Setoid A}
  {f: A ->A} {isf : Proper (respectful equiv equiv) f}
    : (Proper (equiv ==> equiv) (@Nat.iter i A f)).
  Proof.
    intros ? ? E.
    induction i.
    - simpl.
      now rewrite E.
    - simpl.
      apply isf.
      apply IHi.
  Qed.