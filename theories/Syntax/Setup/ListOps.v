From Stdlib Require Export Lists.List Lists.ListDec Arith.
Require Import ssrbool.

(* Given a number n, return the empty list if n is 0 or the singleton list with the predecessor otherwise *)

Definition lpred (n:nat) : list nat.
Proof.
  destruct n as [|n'].
  - exact nil.
  - exact (n' :: nil).
Defined.

Section in_listnat_spec.

Lemma eqn_comm n m : Nat.eqb n m = Nat.eqb m n.
Proof.
  revert m. induction n; destruct m; try reflexivity.
  apply IHn.
Qed.

Lemma in_listnat_spec (l:list nat) (n : nat)
  : reflect
      (In n l)
      (existsb (Nat.eqb n) l).
Proof.
  induction l.
  - apply ReflectF.
    intro H.
    inversion H.
  - apply orPP.
    + rewrite eqn_comm.
      apply Nat.eqb_spec.
    + apply IHl.
Qed.

End in_listnat_spec.