From Stdlib Require Import Nat PeanoNat Arith Lia.

From Category Require Import Lib Theory
  Instance.Sets.

From CwFdeBruijn Require Import
  CatPsh Uwcwf
  Contextual
  Construction.FlippedComprehension
  Structure.FlippedComprehension
  Structure.FlippedComprehension.IterTmUpshift
.

Section T_rel_def.

Context {C : UWCwFN}.

Record Mndf_T_carrier := {
  Mndf_T_m : C;
  Mndf_T_rep : Tm (Mndf_T_m);
}.

Record Mndf_T_rel (a b : Mndf_T_carrier) := {
  Mndf_T_rel_r1 : nat;
  Mndf_T_rel_r2 : nat;
  Mndf_T_rel_m : C;
  
  Mndf_T_rel_Er1m : iter Mndf_T_rel_r1 s (Mndf_T_m a) = Mndf_T_rel_m;
  Mndf_T_rel_Er2m : iter Mndf_T_rel_r2 s (Mndf_T_m b) = Mndf_T_rel_m;
  
  Mndf_T_rel_condition :
    iter_Tm_upshift_Eq Mndf_T_rel_r1 Mndf_T_rel_Er1m
      (Mndf_T_rep a)
    ≈
    iter_Tm_upshift_Eq Mndf_T_rel_r2 Mndf_T_rel_Er2m 
      (Mndf_T_rep b)
}.

End T_rel_def.

Arguments Mndf_T_m {_}.
Arguments Build_Mndf_T_carrier {_ _} _.

Section T_rel_Properties.
Context {C : UWCwFN}.
Let Mndf_T_rel := @Mndf_T_rel C.

Section T_rel_Equivalence.

Lemma Mndf_T_rel_equivalence : Equivalence Mndf_T_rel.
Proof.
  apply Build_Equivalence.
  - intros [m a].
    unshelve eapply (Build_Mndf_T_rel _ _ 0 0 m ); reflexivity.
  - intros [ma a] [mb b] [r1 r2 m Er1m Er2m E]; simpl in *.
    unshelve eapply (Build_Mndf_T_rel _ _ r2 r1 m); simpl; try assumption.
    symmetry. exact E.
  - intros [ma a] [mb b] [mc c]
      [r1 r2 m Er1m Er2m E1]
      [r2' r3 m' Er1m' Er2m' E2];
        simpl in *.
    unshelve eapply
      (Build_Mndf_T_rel _ _ (r1 + r2') (r3 + r2) (iter (r1+r2') s ma) );
      simpl in *.
    + reflexivity.
    + abstract (
        rewrite Nat.add_comm, Nat.iter_add, Er2m',
                Nat.add_comm, Nat.iter_add, Er1m;
        rewrite <- Er2m, <-Er1m', <-!Nat.iter_add, Nat.add_comm;
        reflexivity).
    + unshelve etransitivity.
      { refine (iter_Tm_upshift_Eq (r2+r2') _ b); shelve. }
      * rewrite iter_Tm_upshift_Eq_add_comm.
        symmetry; rewrite iter_Tm_upshift_Eq_add_comm; symmetry.
        erewrite !iter_Tm_upshift_Eq_add.
        rewrite E1.
        reflexivity.
        Unshelve.
        1-2: rewrite Nat.add_comm.
        all: rewrite ?Nat.iter_add.
        all: destruct Er1m, Er1m'; rewrite ?Er2m.
        all: rewrite <-?Nat.iter_add, Nat.add_comm; reflexivity.
      * erewrite iter_Tm_upshift_Eq_add.
        rewrite iter_Tm_upshift_Eq_add_comm.
        erewrite iter_Tm_upshift_Eq_add.
        rewrite E2.
        reflexivity.
        Unshelve.
        all: destruct Er1m', Er1m.
        all: rewrite <-Nat.iter_add, Nat.add_comm, Nat.iter_add, ?Er2m, ?Er2n.
        all: rewrite <-Nat.iter_add, Nat.add_comm; reflexivity.
Qed.
End T_rel_Equivalence.

#[global]
Instance Mndf_T_Setoid :
  Setoid (Mndf_T_carrier) := {|
  equiv := Mndf_T_rel;
  setoid_equiv := Mndf_T_rel_equivalence
|}.

Definition Mndf_T_SetoidObject : SetoidObject := {|
  carrier := Mndf_T_carrier;
|}.

Lemma make_Mndf_T_rel_samectx {m : C} (a b : Tm m)
  (E : a ≈ b)
  : Build_Mndf_T_carrier a ≈ Build_Mndf_T_carrier b.
Proof.
  eapply (Build_Mndf_T_rel _ _ 0 0).
  rewrite !iter_Tm_upshift_Eq_beta_0.
  exact E.
  Unshelve.
  all: reflexivity.
Qed.

Section upshift_to_rel.

Lemma Mndf_T_rel_upshift {m : C} (a : Tm m)
  : Build_Mndf_T_carrier a ≈ Build_Mndf_T_carrier (ftm[Up] a).
Proof.
  eapply (Build_Mndf_T_rel _ _ 1 0); simpl.
  erewrite iter_Tm_upshift_Eq_beta_S, !iter_Tm_upshift_Eq_beta_0.
  reflexivity.
  Unshelve. all: reflexivity.
Qed.

Lemma Mndf_T_rel_iter_upshift' {m : C} (a : Tm m) (i:nat)
  : Build_Mndf_T_carrier a ≈ Build_Mndf_T_carrier (iter_Tm_upshift i a).
Proof.
  eapply (Build_Mndf_T_rel _ _ i 0); simpl.
  erewrite iter_Tm_upshift_Eq_beta_0.
  rewrite <-iter_Tm_upshift_Eq_to_iter_Tm_upshift.
  reflexivity.
  Unshelve. all: reflexivity.
Qed.

Lemma Mndf_T_rel_iter_upshift (a : Mndf_T_carrier) (i:nat)
  : a ≈ Build_Mndf_T_carrier (iter_Tm_upshift i (Mndf_T_rep a)).
Proof.
  apply Mndf_T_rel_iter_upshift'.
Qed.

Lemma Mndf_T_rel_iter_upshift_Eq (a : Mndf_T_carrier) (i:nat) {itism}
  (E : iter i s (Mndf_T_m a) = itism)
  : a ≈ Build_Mndf_T_carrier (iter_Tm_upshift_Eq i E (Mndf_T_rep a)).
Proof.
  eapply (Build_Mndf_T_rel _ _ i 0); simpl.
  erewrite iter_Tm_upshift_Eq_beta_0.
  reflexivity.
  Unshelve. all: reflexivity.
Qed.

Lemma Mndf_T_rel_iter_upshift_Eq' {m} (a : Tm m) (i:nat) {itism}
  (E : iter i s m = itism)
  : Build_Mndf_T_carrier (iter_Tm_upshift_Eq i E a) ≈
    Build_Mndf_T_carrier a .
Proof.
  eapply (Build_Mndf_T_rel _ _ 0 i); simpl.
  erewrite iter_Tm_upshift_Eq_beta_0.
  reflexivity.
  Unshelve. all: reflexivity.
Qed.

End upshift_to_rel.

Section rel_to_upshift.

Lemma Mndf_T_rel_to_Tm_iter_upshift {a b : Mndf_T_carrier}
  (rel : a ≈ b)
  {i:nat}
  (E : iter i s (Mndf_T_m b) = Mndf_T_m a)
  : Mndf_T_rep a ≈ iter_Tm_upshift_Eq i E (Mndf_T_rep b).
Proof.
  destruct rel as [r1 r2 m Er1 Er2 rel].
  destruct Er1.
  assert (H:(r2 = r1 + i)).
  { 
    specialize (f_equal nnp_l Er2).
    specialize (f_equal nnp_l E).
    rewrite !nnp_l_iter.
    lia. }
  induction (eq_sym H); clear H.
  eapply (iter_Tm_upshift_Eq_inj _ _).
  erewrite <-iter_Tm_upshift_Eq_add.
  exact rel.
Qed.

Lemma Mndf_T_rel_to_iter_upshift_cases {a b : Mndf_T_carrier} (rel : a ≈ b)
  : (∃ i E,
      Mndf_T_rep a ≈ iter_Tm_upshift_Eq i E (Mndf_T_rep b))
    ∨ (∃ i E,
      Mndf_T_rep b ≈ iter_Tm_upshift_Eq i E (Mndf_T_rep a)).
Proof.
  destruct (Compare_dec.le_ge_dec (nnp_l (Mndf_T_m a)) (nnp_l(Mndf_T_m b))) as [right|left].
  - right.
    split with (nnp_l (Mndf_T_m b) -nnp_l (Mndf_T_m a)).
    esplit.
    apply Mndf_T_rel_to_Tm_iter_upshift.
    exact (symmetry rel).
    Unshelve.
    apply nnp_l_injective.
    rewrite !nnp_l_iter.
    lia.
  - left.
    split with (nnp_l (Mndf_T_m a) - nnp_l (Mndf_T_m b)).
    esplit.
    apply Mndf_T_rel_to_Tm_iter_upshift.
    exact (rel).
    Unshelve.
    apply nnp_l_injective.
    rewrite ! nnp_l_iter.
    lia.
Qed.

Lemma Mndf_T_rel_samectx {m : C} (a b : Tm m)
  (E : Build_Mndf_T_carrier b ≈ Build_Mndf_T_carrier a)
  : b ≈ a.
Proof.
  apply (Mndf_T_rel_to_Tm_iter_upshift E (i:=0) eq_refl).
Qed.

End rel_to_upshift.

End T_rel_Properties.