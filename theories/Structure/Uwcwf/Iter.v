From Stdlib Require Import Nat PeanoNat.
From Category Require Import Theory Lib.
From CwFdeBruijn Require Import CatPsh Uwcwf Structure.Uwcwf Structure.Uwcwf.Transport.
From CwFdeBruijn Require Import Contextual.

Open Scope nat.

Section Iter_π1.

Context {C : UWCwF}.

Definition iter_π1 {m : C} (i:nat)
  : forall {n}, m ~> iter i s n -> m ~> n.
Proof.
  induction i.
  - intros ? δ. exact δ.
  - intros n δ.
    exact (IHi _ (π1 δ)).
Defined.

#[global]
Instance proper_iter_π1 {m: C} {i n} : Proper (equiv ==> equiv) (@iter_π1 m i n).
Proof.
  intros ? ? E.
  induction i; simpl.
  - proper.
  - apply IHi.
    rewrite E.
    proper.
Qed.

Lemma iter_pi1_beta_S {m n : C} {i:nat} (δ : m ~> iter (S i) s n)
  : iter_π1 (S i) δ = iter_π1 i (π1 δ).
Proof.
  reflexivity.
Defined.


Lemma iter_pi1_comp {m' m n : C} (i:nat) (δ : m ~> iter i s n) (γ : m' ~> m)
  : (iter_π1 i δ) ∘ γ ≈ iter_π1 i (δ ∘ γ).
Proof.
  induction i.
  - reflexivity.
  - simpl.
    etransitivity.
    { exact (IHi (π1 δ)). }
    rewrite pi1_comp.
    reflexivity.
Qed. 

End Iter_π1.

Lemma iter_π1_swap' {C : UWCwFN} {m n : C} {i:nat} (δ : m ~> iter (S i) s n)
  (p : iter (S i) s n = iter i s (s n))
  : iter_π1 (S i) δ = π1 (iter_π1 i (Logic.transport (λ x , m ~> x) p δ)).
Proof.
  simpl.
  induction i.
  - simpl.
    cbn in p.
    rewrite (UIP_refl_ctx p).
    reflexivity.
  - simpl.
    erewrite pi1_transport_nnp.
    apply (IHi (π1 δ)).
    Unshelve.
    symmetry.
    apply Nat.iter_swap.
Qed.

Lemma iter_π1_swap {C : UWCwFN} {m n : C} {i:nat}
  (δ : m ~> iter (S i) s n)
  : iter_π1 (S i) δ = π1 (iter_π1 i (Logic.transport (λ x , m ~> x) (Nat.iter_succ_r i _ s n) δ)).
Proof. exact (iter_π1_swap' δ (Nat.iter_succ_r i _ s n)). Qed.  

Section Iter_π1_withEq_def.

  Context {C : UWCwF}.
  
  Definition iter_π1_Eq {m n : C} (i:nat) {itisn : C} (E : itisn = iter i s n) (δ : m ~> itisn)
  : m ~> n
  := iter_π1 i (Logic.transport (λ x, m ~> x) E δ).
  #[global]
  Instance proper_iter_π1_Eq {m n: C} (i:nat) {itisn : C} {E' : itisn = iter i s n}
  : Proper (equiv ==> equiv) (@iter_π1_Eq m n i itisn E').
  Proof.
    intros ? ? E.
    unfold iter_π1_Eq.
    rewrite E.
    reflexivity.
  Qed.

  Definition iter_π1_Eq_beta_0' {m n itisn : C} (E : itisn = iter 0 s n) (δ : m ~> itisn)
  : iter_π1_Eq 0 E δ = (Logic.transport (λ x, m ~> x) E δ).
  Proof.
    reflexivity.
  Defined.

End Iter_π1_withEq_def.
Section Iter_π1_withEq_properties.
  Context {C : UWCwFN}.

  Lemma iter_π1_Eq_beta_0 {m n : C} (E : n = iter 0 s n) (δ : m ~> n)
  : iter_π1_Eq 0 E δ = δ.
  Proof.
    rewrite iter_π1_Eq_beta_0'.
    rewrite (UIP_refl_ctx E).
    reflexivity.
  Qed.

  Lemma iter_π1_Eq_beta_S_refl {m n itisn: C} (i:nat) (E : itisn = iter (S i) s n) (δ : m ~> itisn)
  : iter_π1_Eq (S i) E δ = iter_π1_Eq i eq_refl (π1 (Logic.transport (λ x, m~>x) E δ)).
  Proof.
    reflexivity.
  Defined.

  Lemma iter_pi1_Eq_beta_S {m n itisn: C} (i:nat)
    (E : itisn = iter i s n) (E' : s itisn = iter (S i) s n)
    (δ : m ~> s itisn)
  : iter_π1_Eq (S i) E' δ = iter_π1_Eq i E (π1 δ).
  Proof.
    unfold iter_π1_Eq.
    simpl.
    f_equal.
    erewrite pi1_transport_nnp.
    reflexivity.
  Qed.

  Lemma iter_π1_swap_toEq {m n : C} {i:nat}
  (δ : m ~> iter (S i) s n)
  : iter_π1 (S i) δ = π1 (iter_π1_Eq i (Nat.iter_succ_r i _ s n) δ).
  Proof.
    apply iter_π1_swap.
  Qed.

  Lemma iter_pi1_Eq_swap {m n itisn: C} (i:nat)
    (E : itisn = (iter (S i) s n))
    (E' : itisn = iter i s (s n))
    (δ : m ~> itisn)
  : iter_π1_Eq (S i) E δ = (π1 (iter_π1_Eq i E' δ)).
  Proof.
    unfold iter_π1_Eq.
    rewrite iter_π1_swap.
    repeat f_equal.
    rewrite transport_trans.
    f_equal.
    apply UIP_ctx.
  Qed.

  Lemma iter_π1_Eq_to_iter_π1 {m n : C} (i:nat) (δ : m ~> iter i s n)
  : iter_π1_Eq i eq_refl δ = iter_π1 i δ.
  Proof.
    reflexivity.
  Defined.
  Lemma iter_π1_Eq_to_iter_π1' {m n : C} (i:nat) (δ : m ~> iter i s n)
  (E : iter i s n = iter i s n)
  : iter_π1_Eq i E δ = iter_π1 i δ.
  Proof.
    rewrite (UIP_refl_ctx E).
    reflexivity.
  Qed.

  Lemma iter_pi1_Eq_UIP {m n itisn : C} (i:nat) (δ : m ~> itisn)
  (E1 E2 : itisn = iter i s n)
  : iter_π1_Eq i E1 δ = iter_π1_Eq i E2 δ.
  Proof.
    rewrite (UIP_ctx _ _ E1 E2).
    reflexivity.
  Qed.

  Lemma iter_pi1_Eq_rew {m n itisn : C} (i j:nat) (δ : m ~> itisn)
  (En : i = j)
  (Ei : itisn = iter i s n)
  (Ej : itisn = iter j s n)
  : iter_π1_Eq i Ei δ = iter_π1_Eq j Ej δ.
  Proof.
    revert Ei Ej.
    rewrite En; intros.
    apply (iter_pi1_Eq_UIP _ _ Ei Ej).
  Qed.

  Lemma iter_pi1_Eq_comp {m' m n itisn : C} (i:nat)
  (E: itisn = iter i s n)
  (δ : m ~> itisn)
  (γ : m' ~> m)
  : (iter_π1_Eq i E δ) ∘ γ ≈ iter_π1_Eq i E (δ ∘ γ).
  Proof.
    revert δ.
    rewrite E.
    intro δ.
    apply iter_pi1_comp.
  Qed.
End Iter_π1_withEq_properties.

Section Iter_nnp_π1.
Context {C: UWCwFN} {m : C} {n:nat}.

Definition iter_nnp_π1 (i:nat) (δ : m ~> ctl_c (i+n)) 
  : m ~> (ctl_c n)
  := iter_π1 i (Logic.transport _ (ctl_c_add i n) δ).
#[global]
Instance proper_iter_nnp_π1 {i:nat} : Proper (equiv ==> equiv) (@iter_nnp_π1 i).
Proof.
  intros ? ? E.
  unfold iter_nnp_π1.
  rewrite E.
  reflexivity.
Qed.

Lemma iter_nnp_π1_beta_0 (δ : m ~> ctl_c n) 
  : iter_nnp_π1 0 δ = δ.
Proof.
  reflexivity.
Defined.

Lemma iter_nnp_π1_beta_S (i:nat) (δ : m ~> ctl_c (S i + n))
  : iter_nnp_π1 (S i) δ ≈ iter_nnp_π1 i (π1 δ).
Proof.
  induction i.
  - reflexivity.
  - unfold iter_nnp_π1.

    simpl.
    f_equiv.
    f_equiv.
    rewrite <-!transport_trans.
    rewrite <-transport_f_equal.
    rewrite <-!transport_trans.
    simpl. 

    rewrite transport_f_equal.
    rewrite pi1_transport.
    reflexivity.
Qed.

End Iter_nnp_π1.
Close Scope nat.
