From Stdlib Require Import Nat PeanoNat Arith Lia.

From Category Require Import Lib Theory
  Instance.Sets.

From CwFdeBruijn Require Import
  CatPsh Uwcwf
  Contextual
  Construction.FlippedComprehension
  Structure.FlippedComprehension
  Structure.FlippedComprehension.IterUpshift
.

Section S_rel_def.

Context {C : UWCwFN}.

Record Mndf_S_carrier := {
  Mndf_S_m : C;
  Mndf_S_n : C;
  Mndf_S_rep : Mndf_S_m ~> Mndf_S_n;
}.

Record Mndf_S_rel (δ γ : Mndf_S_carrier) := {
  Mndf_S_rel_r1 : nat;
  Mndf_S_rel_r2 : nat;
  Mndf_S_rel_m : C;
  Mndf_S_rel_n : C;
  Mndf_S_rel_Er1m : iter Mndf_S_rel_r1 s (Mndf_S_m δ) = Mndf_S_rel_m;
  Mndf_S_rel_Er1n : iter Mndf_S_rel_r1 s (Mndf_S_n δ) = Mndf_S_rel_n;
  Mndf_S_rel_Er2m : iter Mndf_S_rel_r2 s (Mndf_S_m γ) = Mndf_S_rel_m;
  Mndf_S_rel_Er2n : iter Mndf_S_rel_r2 s (Mndf_S_n γ) = Mndf_S_rel_n;
  Mndf_S_rel_condition :
    iter_upshift_Eq Mndf_S_rel_r1
      Mndf_S_rel_Er1m Mndf_S_rel_Er1n
      (Mndf_S_rep δ)
    ≈
    iter_upshift_Eq Mndf_S_rel_r2
      Mndf_S_rel_Er2m Mndf_S_rel_Er2n
      (Mndf_S_rep γ)
}.

Definition make_Mndf_S_rel_from_optimal_r (δ γ : Mndf_S_carrier)
  {Er1m} {Er1n} {Er2m} {Er2n}
  (condition :
    iter_upshift_Eq _ Er1m Er1n (Mndf_S_rep δ)
    ≈ iter_upshift_Eq _ Er2m Er2n (Mndf_S_rep γ))
  : Mndf_S_rel δ γ := {|
    Mndf_S_rel_r1 := max_ctx_diff_l (Mndf_S_m δ) (Mndf_S_m γ);
    Mndf_S_rel_r2 := max_ctx_diff_r (Mndf_S_m δ) (Mndf_S_m γ);
    Mndf_S_rel_m := max_ctx (Mndf_S_m δ) (Mndf_S_m γ);
    Mndf_S_rel_n := max_ctx (Mndf_S_n δ) (Mndf_S_n γ);
    Mndf_S_rel_Er1m := Er1m;
    Mndf_S_rel_Er1n := Er1n;
    Mndf_S_rel_Er2m := Er2m;
    Mndf_S_rel_Er2n := Er2n;
    Mndf_S_rel_condition := condition
  |}.

End S_rel_def.
Arguments Mndf_S_m {_}.
Arguments Mndf_S_n {_}.
Arguments Build_Mndf_S_carrier {_ _ _}.

Section S_rel_Properties.
Context {C : UWCwFN}.
Let Mndf_S_rel := @Mndf_S_rel C.

Section S_rel_Equivalence.

Lemma Mndf_S_rel_equivalence : Equivalence Mndf_S_rel.
Proof.
  apply Build_Equivalence.
  - intros [m n δ].
    unshelve eapply (Build_Mndf_S_rel _ _ 0 0 m n); reflexivity.
  - intros [m n δ] [m' n' γ] [r1 r2 mr nr Er1m Er1n Er2m Er2n E]; simpl in *.
    unshelve eapply (Build_Mndf_S_rel _ _ r2 r1 mr nr); simpl; try assumption.
    symmetry. exact E.
  - intros [m n δ] [m' n' γ] [m'' n'' η]
      [r1 r2 mr nr Er1m Er1n Er2m Er2n E1]
      [r2' r3 mr' nr' Er1m' Er1n' Er2m' Er2n' E2];
        simpl in *.
    unshelve eapply
      (Build_Mndf_S_rel _ _ (r1 + r2') (r3 + r2) (iter (r1+r2') s m) (iter (r1+r2') s n));
      simpl in *.
    all: try reflexivity.
    + rewrite Nat.add_comm, Nat.iter_add, Er2m',
              Nat.add_comm, Nat.iter_add, Er1m.
      rewrite <- Er2m, <-Er1m', <-!Nat.iter_add, Nat.add_comm.
      reflexivity.
    + rewrite Nat.add_comm, Nat.iter_add, Er2n',
              Nat.add_comm, Nat.iter_add, Er1n.
      rewrite <- Er2n, <-Er1n', <-!Nat.iter_add, Nat.add_comm.
      reflexivity.
    + unshelve etransitivity.
      { refine (iter_upshift_Eq (r2+r2') _ _ γ); shelve. }
      * rewrite iter_upshift_Eq_add_comm.
        symmetry; rewrite iter_upshift_Eq_add_comm; symmetry.
        erewrite !iter_upshift_Eq_add.
        rewrite E1.
        reflexivity.
        Unshelve.
        1-2: rewrite Nat.add_comm.
        all: rewrite ?Nat.iter_add.
        all: destruct Er1m, Er1n, Er1m', Er1n'; rewrite ?Er2m, ?Er2n.
        all: rewrite <-?Nat.iter_add, Nat.add_comm; reflexivity.
      * erewrite iter_upshift_Eq_add.
        rewrite iter_upshift_Eq_add_comm.
        erewrite iter_upshift_Eq_add.
        rewrite E2.
        reflexivity.
        Unshelve.
        all: destruct Er1m', Er1n', Er1m, Er1n.
        all: rewrite <-Nat.iter_add, Nat.add_comm, Nat.iter_add, ?Er2m, ?Er2n.
        all: rewrite <-Nat.iter_add, Nat.add_comm; reflexivity.
Qed.

Global Instance Mndf_S_Setoid :
  Setoid (Mndf_S_carrier) := {|
  equiv := Mndf_S_rel;
  setoid_equiv := Mndf_S_rel_equivalence
|}.

End S_rel_Equivalence.


Lemma make_Mndf_S_rel_samectx {m n : C} (δ γ : m ~> n)
  (E : δ ≈ γ)
  : Build_Mndf_S_carrier δ ≈ Build_Mndf_S_carrier γ.
Proof.
  eapply (Build_Mndf_S_rel _ _ 0 0).
  rewrite !iter_upshift_Eq_beta_0.
  exact E.
  Unshelve.
  all: reflexivity.
Qed.


Section upshift_to_rel.

Lemma Mndf_S_rel_upshift {m n : C} (δ : m~>n)
  : Build_Mndf_S_carrier δ ≈ Build_Mndf_S_carrier (upshift δ).
Proof.
  eapply (Build_Mndf_S_rel _ _ 1 0); simpl.
  erewrite iter_upshift_Eq_beta_S, !iter_upshift_Eq_beta_0.
  reflexivity.
  Unshelve. all: reflexivity.
Qed.

Lemma Mndf_S_rel_iter_upshift' {m n : C} (δ : m~>n) (i:nat)
  : Build_Mndf_S_carrier δ ≈ Build_Mndf_S_carrier (iter_upshift i δ).
Proof.
  eapply (Build_Mndf_S_rel _ _ i 0); simpl.
  erewrite iter_upshift_Eq_beta_0.
  rewrite <-iter_upshift_Eq_to_iter_upshift.
  reflexivity.
  Unshelve. all: reflexivity.
Qed.

Lemma Mndf_S_rel_iter_upshift (δ : Mndf_S_carrier) (i:nat)
  : δ ≈ Build_Mndf_S_carrier (iter_upshift i (Mndf_S_rep δ)).
Proof.
  apply Mndf_S_rel_iter_upshift'.
Qed.

Lemma Mndf_S_rel_iter_upshift_Eq (δ : Mndf_S_carrier) (i:nat) {itism itisn}
  (Em : iter i s (Mndf_S_m δ) = itism)
  (En : iter i s (Mndf_S_n δ) = itisn)
  : δ ≈ Build_Mndf_S_carrier (iter_upshift_Eq i Em En (Mndf_S_rep δ)).
Proof.
  eapply (Build_Mndf_S_rel _ _ i 0); simpl.
  erewrite iter_upshift_Eq_beta_0.
  reflexivity.
  Unshelve. all: reflexivity.
Qed.

Lemma Mndf_S_rel_iter_upshift_Eq' {m n} (δ : m ~> n) (i:nat) {itism itisn}
  (Em : iter i s m = itism)
  (En : iter i s n = itisn)
  : Build_Mndf_S_carrier (iter_upshift_Eq i Em En δ)
    ≈ Build_Mndf_S_carrier δ.
Proof.
  eapply (Build_Mndf_S_rel _ _ 0 i); simpl.
  erewrite iter_upshift_Eq_beta_0.
  reflexivity.
  Unshelve. all: reflexivity.
Qed.

End upshift_to_rel.

Lemma Mndf_S_rel_lctx {δ γ : Mndf_S_carrier} (E : δ ≈ γ)
  : nnp_l (Mndf_S_m δ) + nnp_l (Mndf_S_n γ)
  = nnp_l (Mndf_S_m γ) + nnp_l (Mndf_S_n δ).
Proof.
  assert (Er1m := f_equal nnp_l (Mndf_S_rel_Er1m _ _ E)).
  assert (Er1n := f_equal nnp_l (Mndf_S_rel_Er1n _ _ E)).
  assert (Er2m := f_equal nnp_l (Mndf_S_rel_Er2m _ _ E)).
  assert (Er2n := f_equal nnp_l (Mndf_S_rel_Er2n _ _ E)).
  rewrite !nnp_l_iter in *.
  lia.
Qed.

Section rel_to_upshift.

Lemma Mndf_S_rel_to_iter_upshift {δ γ : Mndf_S_carrier}
  (a : Tm (Mndf_S_m δ))
  (rel : δ ≈ γ)
  {i:nat}
  (Em : iter i s (Mndf_S_m γ) = Mndf_S_m δ)
  (En : iter i s (Mndf_S_n γ) = Mndf_S_n δ)
  : Mndf_S_rep δ ≈ iter_upshift_Eq i Em En (Mndf_S_rep γ).
Proof.
  destruct rel as [r1 r2 mr nr Er1m Er1n Er2m Er2n rel].
  destruct Er1m, Er1n.
  assert (H:(r2 = r1 + i)).
  { specialize (f_equal nnp_l Er2m).
    specialize (f_equal nnp_l Er2n).
    specialize (f_equal nnp_l Em).
    specialize (f_equal nnp_l En).
    rewrite !nnp_l_iter.
    lia. }
  induction (eq_sym H); clear H.

  eapply (iter_upshift_Eq_inj _ a _ _).
  erewrite <-iter_upshift_Eq_add.
  exact rel.
Qed.

Lemma Mndf_S_rel_to_upshift_iter_upshift {δ γ : Mndf_S_carrier}
  (rel : δ ≈ γ)
  {i:nat}
  (Em : iter (S i) s (Mndf_S_m γ) = s (Mndf_S_m δ))
  (En : iter (S i) s (Mndf_S_n γ) = s (Mndf_S_n δ))
  : upshift (Mndf_S_rep δ) ≈ iter_upshift_Eq (S i) Em En (Mndf_S_rep γ).
Proof.
  change (S i) with (1+i).
  erewrite iter_upshift_Eq_add_comm'.
  erewrite iter_upshift_Eq_add.
  erewrite iter_upshift_Eq_beta_S, iter_upshift_Eq_beta_0.

  assert (Uprel : Build_Mndf_S_carrier (↑ (Mndf_S_rep δ)) ≈ Build_Mndf_S_carrier (↑ (Mndf_S_rep γ))).
  { 
    etransitivity; [etransitivity; [symmetry |exact rel]|];
      apply Mndf_S_rel_upshift. }

  refine (Mndf_S_rel_to_iter_upshift _ Uprel _ _).
  simpl.
  apply (π2 id).
  Unshelve.
  all: try reflexivity.
  all: apply nnp_l_injective;
    specialize (f_equal nnp_l Em);
    specialize (f_equal nnp_l En);
    rewrite ?nnp_l_iter, ?nnp_l_s.
  all: lia.
Qed.

Lemma Mndf_S_rel_to_upshift_iter_upshift_cases {δ γ : Mndf_S_carrier} (rel : δ ≈ γ)
  : (∃ i Emi Eni,
      upshift (Mndf_S_rep δ) ≈ iter_upshift_Eq (S i) Emi Eni (Mndf_S_rep γ))
    ∨ (∃ i Emi Eni,
      upshift (Mndf_S_rep γ) ≈ iter_upshift_Eq (S i) Emi Eni (Mndf_S_rep δ)).
Proof.
  destruct (Compare_dec.le_ge_dec (nnp_l (Mndf_S_m δ)) (nnp_l(Mndf_S_m γ))) as [right|left].
  - right.
    split with (nnp_l (Mndf_S_m γ) -nnp_l (Mndf_S_m δ)).
    esplit; esplit.
    apply Mndf_S_rel_to_upshift_iter_upshift.
    exact (symmetry rel).
    Unshelve.
    + apply nnp_l_injective.
      rewrite !nnp_l_iter, nnp_l_s.
      lia.
    + apply nnp_l_injective.
      specialize (Mndf_S_rel_lctx rel).
      rewrite !nnp_l_iter, nnp_l_s.
      lia.
  - left.
    split with (nnp_l (Mndf_S_m δ) - nnp_l (Mndf_S_m γ)).
    esplit; esplit.
    apply Mndf_S_rel_to_upshift_iter_upshift.
    exact (rel).
    Unshelve.
    + apply nnp_l_injective.
      rewrite ! nnp_l_iter, nnp_l_s.
      lia.
    + apply nnp_l_injective.
      specialize (Mndf_S_rel_lctx rel).
      rewrite ! nnp_l_iter, nnp_l_s.
      lia.
Qed.

Lemma Mndf_S_rel_samectx {m n :C} (γ δ : m ~> n)
  (a : Tm m)
  (E : Build_Mndf_S_carrier γ ≈ Build_Mndf_S_carrier δ)
  : γ ≈ δ.
Proof.
  refine (Mndf_S_rel_to_iter_upshift _ E (i:=0) eq_refl eq_refl).
  exact a.
Qed.

Lemma Mndf_S_rel_samectx_extsrc {m n :C} (γ δ : s m ~> n)
  (E : Build_Mndf_S_carrier γ ≈ Build_Mndf_S_carrier δ)
  : γ ≈ δ.
Proof.
  refine (Mndf_S_rel_to_iter_upshift _ E (i:=0) eq_refl eq_refl).
  exact (π2 id).
Qed.

Lemma Mndf_S_rel_samectx_exttgt {m n :C} (γ δ : m ~> s n)
  (E : Build_Mndf_S_carrier γ ≈ Build_Mndf_S_carrier δ)
  : γ ≈ δ.
Proof.
  refine (Mndf_S_rel_to_iter_upshift _ E (i:=0) eq_refl eq_refl).
  exact (π2 δ).
Qed.

End rel_to_upshift.
End S_rel_Properties.