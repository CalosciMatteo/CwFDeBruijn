From Stdlib Require Import Nat PeanoNat Lia.
From Category Require Import Theory Lib.
From Category.Instance Require Import
  Sets.
From CwFdeBruijn Require Import 
  CatPsh Uwcwf
  Lib.Setoid Lib.Transport
  Structure.Uwcwf Structure.Uwcwf.Transport.
From CwFdeBruijn Require Import 
  Contextual
  Construction.FlippedComprehension
  Structure.FlippedComprehension
  Structure.FlippedComprehension.IterUpshift
.

Open Scope nat.

Section Iter_Tm_Upshift.

Context {C : UWCwFN}.

Definition iter_Tm_upshift {m : ctx C} (i:nat) (a : Tm m) : Tm (iter i s m).
Proof.
  induction i.
  - exact a.
  - exact (ftm[ Up ] IHi).
Defined.

#[global]
Instance proper_iter_Tm_upshift {i} {m: C} : Proper (equiv ==> equiv) (@iter_Tm_upshift m i).
Proof.
  intros ? ? E.
  induction i; simpl.
  - proper.
  - f_equiv.
    apply IHi.
Qed.

Lemma iter_Tm_upshift_beta_S {m : C} {i:nat} (a : Tm m)
  : iter_Tm_upshift (S i) a = ftm[ Up ] (iter_Tm_upshift i a).
Proof.
  reflexivity.
Defined.

Lemma iter_upshift_subst {m n : C} (i:nat)
  (a : Tm n) (δ : m ~> n)
  : (iter_Tm_upshift i a) [(iter_upshift i δ)] ≈ iter_Tm_upshift i (a[δ]).
Proof.
  induction i.
  - reflexivity.
  - simpl.
    unfold Up_tm_ntr_data.
    rewrite <-Tm_upshift_subst.
    f_equiv.
    apply IHi.
Qed.

Lemma pi2_iter_upshift' {m n : C} (δ : m ~> s n) (i:nat)
  (E : iter i s (s n) = s (iter i s n))
  : π2 (Logic.transport (λ x, iter i s m ~> x) E (iter_upshift i δ)) ≈ iter_Tm_upshift i (π2 δ).
Proof.
  induction i.
  - rewrite (UIP_refl_ctx E).
    reflexivity.
  - simpl.
    erewrite <-IHi.
    unfold Up_tm_ntr_data; rewrite <-pi2_upshift.
    f_equiv.
    change (Logic.transport (λ x, _ ~{ C }~> x) E (↑ (iter_upshift i δ)))
      with (homcast eq_refl E (↑ (iter_upshift i δ))).
    
    erewrite <-(upshift_transport (iter_upshift i δ) eq_refl eq_refl (Nat.iter_swap _ _ _ _)).
    f_equiv.
    simpl.
    reflexivity.
Qed.

Lemma pi2_iter_upshift {m n : C} (δ : m ~> s n) (i:nat)
  : π2 (Logic.transport (λ x, iter i s m ~> x) (Nat.iter_swap _ _ _ _) (iter_upshift i δ)) ≈ iter_Tm_upshift i (π2 δ).
Proof.
  apply pi2_iter_upshift'.
Qed.

End Iter_Tm_Upshift.

Section Iter_Tm_Upshift_withEq_def.

  Context {C : UWCwFN}.
  
  Definition iter_Tm_upshift_Eq {m : C} (i:nat) {itism : C}
    (Em : iter i s m = itism)
    (a : Tm m)
  : Tm itism
  := Logic.transport (λ x, Tm x) Em (iter_Tm_upshift i a).
  #[global]
  Instance proper_iter_Tm_upshift_Eq {m: C} (i:nat) {itism : C}
    (Em : iter i s m = itism)
  : Proper (equiv ==> equiv) (@iter_Tm_upshift_Eq m i itism Em).
  Proof.
    intros ? ? E.
    unfold iter_Tm_upshift_Eq.
    destruct Em.
    simpl.
    rewrite E.
    reflexivity.
  Qed.

  Definition iter_Tm_upshift_Eq_beta_0' {m itism : C}
    (Em : iter 0 s m = itism)
    (δ : Tm m )
  : iter_Tm_upshift_Eq 0 Em δ 
  = Logic.transport (λ x, Tm x) Em (iter_Tm_upshift 0 δ).
  Proof.
    reflexivity.
  Defined.

End Iter_Tm_Upshift_withEq_def.

Section Iter_Tm_Upshift_withEq_properties.
  Context {C : UWCwFN}.

  Lemma iter_Tm_upshift_Eq_beta_0 {m: C}
    (Em : iter 0 s m = m)
    (δ : Tm m )
  : iter_Tm_upshift_Eq 0 Em δ = δ.
  Proof.
    rewrite iter_Tm_upshift_Eq_beta_0'.
    rewrite (UIP_refl_ctx Em).
    reflexivity.
  Qed.

  Lemma iter_Tm_upshift_Eq_beta_S_refl {m itism : C} (i:nat)
    (Em : iter (S i) s m = itism)
    (a : Tm m)
  : iter_Tm_upshift_Eq (S i) Em a
  = Logic.transport (λ x, Tm x) Em 
      (ftm[ Up ] (iter_Tm_upshift_Eq i eq_refl a)). 
  Proof.
    reflexivity.
  Defined.

  Lemma iter_Tm_upshift_swap' {m : C} {i:nat}
  (pm : iter i s (s m) = iter (S i) s m)
  (a : Tm m)
  : iter_Tm_upshift (S i) a
  = Logic.transport (λ x , Tm x) pm (iter_Tm_upshift i (ftm[ Up ] a)).
  Proof.
    induction i.
    - simpl.
      rewrite (UIP_refl_ctx pm).
      reflexivity.
    - simpl.
      change (
        ftm[Up] (ftm[Up] (iter_Tm_upshift i a))
        = Logic.transport (λ x, fobj[Tm] x) pm
            (ftm[ Up] (iter_Tm_upshift i (Up_tm_ntr_data m a)))
      ).
      etransitivity.
      2: apply Tm_upshift_transport.
      f_equal.
      apply IHi.
      Unshelve. all: apply Nat.iter_swap.
  Qed.

  Lemma iter_Tm_upshift_swap {m : C} {i:nat}
    (a : Tm m)
    : iter_Tm_upshift (S i) a
    = (Logic.transport (λ x , Tm x) (eq_sym (Nat.iter_succ_r i _ s m))
        (iter_Tm_upshift i (ftm[Up] a))).
  Proof. 
    apply iter_Tm_upshift_swap'.
  Qed.

  Lemma iter_Tm_upshift_Eq_beta_S {m itism: C} (i:nat)
    (Em : iter i s m = itism) (Em' : iter (S i) s m = s itism)
    (a : Tm m)
  : iter_Tm_upshift_Eq (S i) Em' a = ftm[Up] (iter_Tm_upshift_Eq i Em a).
  Proof.
    unfold iter_Tm_upshift_Eq.
    erewrite Tm_upshift_transport.
    reflexivity.
  Qed.

  Lemma iter_Tm_upshift_swap_toEq {m n : C} {i:nat}
  (a : Tm m)
  : iter_Tm_upshift (S i) a
  = iter_Tm_upshift_Eq i
      (eq_sym (Nat.iter_succ_r i _ s m))
      (ftm[Up] a).
  Proof.
    apply iter_Tm_upshift_swap.
  Qed.

  Lemma iter_Tm_upshift_Eq_swap {m itism : C} (i:nat)
    (Em : iter (S i) s m = itism) (Em' : iter i s (s m) = itism)
    (a : Tm m)
  : iter_Tm_upshift_Eq (S i) Em a = (iter_Tm_upshift_Eq i Em' (ftm[Up] a)).
  Proof.
    destruct Em.
    simpl.
    unfold iter_Tm_upshift_Eq.
    etransitivity.
    2:{ exact (iter_Tm_upshift_swap' Em' a). }
    reflexivity.
  Qed.

  Lemma iter_Tm_upshift_Eq_to_iter_Tm_upshift {m : C} (i:nat) (a :Tm m)
  : iter_Tm_upshift_Eq i eq_refl a = iter_Tm_upshift i a.
  Proof.
    reflexivity.
  Defined.
  Lemma iter_Tm_upshift_Eq_to_iter_Tm_upshift' {m : C} (i:nat) (a : Tm m)
  (Em : iter i s m = iter i s m)
  : iter_Tm_upshift_Eq i Em a = iter_Tm_upshift i a.
  Proof.
    rewrite (UIP_refl_ctx Em).
    reflexivity.
  Qed.

  Lemma iter_Tm_upshift_Eq_UIP {m itism : C} (i:nat) (a : Tm m)
  (Em1 Em2 : iter i s m = itism)
  : iter_Tm_upshift_Eq i Em1 a = iter_Tm_upshift_Eq i Em2 a.
  Proof.
    rewrite (UIP_ctx _ _ Em1 Em2).
    reflexivity.
  Qed.

  Lemma iter_Tm_upshift_Eq_rew {m itism : C} (i j:nat) (a : Tm m)
  (p : i = j)
  (Eim : iter i s m = itism) (Ejm : iter j s m = itism)
  : iter_Tm_upshift_Eq i Eim a = iter_Tm_upshift_Eq j Ejm a.
  Proof.
    revert Eim Ejm.
    rewrite p; intros.
    apply (iter_Tm_upshift_Eq_UIP _ _ _ _).
  Qed.

  Lemma iter_Tm_upshift_Eq_rew' {m itism : C} (i j:nat) (a : Tm m)
  (p : i = j)
  (Eim : iter i s m = itism) (Ejm : iter j s m = itism)
  : iter_Tm_upshift_Eq i Eim a ≈ iter_Tm_upshift_Eq j Ejm a.
  Proof.
    revert Eim Ejm.
    rewrite p; intros.
    erewrite (iter_Tm_upshift_Eq_UIP _ _ _ _).
    reflexivity.
  Qed.

  Lemma iter_Tm_upshift_Eq_subst {m n itism itisn : C} (i:nat)
    (Em : iter i s m = itism)
    (En : iter i s n = itisn)
    
    (a : Tm n)
    (δ : m ~> n)
  : (iter_Tm_upshift_Eq i En a) [(iter_upshift_Eq i Em En δ)] ≈ iter_Tm_upshift_Eq i Em (a[δ]).
  Proof.
    revert a δ.
    destruct Em, En.
    intros a δ.
    apply iter_upshift_subst.
  Qed.

  Lemma iter_Tm_upshift_add {m : C} (i j : nat)
    (E : iter i s (iter j s m) = iter (i + j) s m)
    (a : Tm m)
  : iter_Tm_upshift (i + j) a =
    iter_Tm_upshift_Eq i E (iter_Tm_upshift j a).
  Proof.
    revert i a E.
    induction j; intros i a E.
    - revert E; rewrite Nat.add_0_r; intros E.
      simpl.
      symmetry.
      rewrite <-iter_Tm_upshift_Eq_to_iter_Tm_upshift.
      apply iter_Tm_upshift_Eq_UIP.
    - revert E; rewrite Nat.add_succ_r; intros E.
      simpl.
      etransitivity; [| apply iter_Tm_upshift_Eq_swap].
      erewrite iter_Tm_upshift_Eq_beta_S.
      apply (f_equal ftm[Up] (IHj _ _ _ )).
    Unshelve. all: simpl; rewrite Nat.iter_add; reflexivity.
  Qed.

  Lemma iter_Tm_upshift_Eq_add {m itjsm itijsm : C} (i j: nat)
    (Em_j : iter j s m = itjsm)
    (Em_ij: iter (i + j) s m = itijsm)
    (Em_i : iter i s itjsm = itijsm)
    (a : Tm m)
  : iter_Tm_upshift_Eq (i + j) Em_ij a =
    iter_Tm_upshift_Eq i Em_i (iter_Tm_upshift_Eq j Em_j a).
  Proof.
    destruct Em_j, Em_ij.
    simpl.
    apply iter_Tm_upshift_add.
  Qed.

  Lemma iter_Tm_upshift_Eq_add_comm' {m itijsm : C} (i j : nat)
    (Em : iter (i+j) s m = itijsm)
    (Em' : iter (j + i) s m = itijsm)
    (a : Tm m)
  : iter_Tm_upshift_Eq (j + i) Em' a =
    iter_Tm_upshift_Eq (i + j) Em a.
  Proof.
    revert Em Em'.
    rewrite Nat.add_comm; intros.
    apply iter_Tm_upshift_Eq_UIP.
  Qed.

  Lemma iter_Tm_upshift_Eq_add_comm {m itijsm : C} (i j : nat)
    (Em : iter (i+j) s m = itijsm)
    (a : Tm m)
  : iter_Tm_upshift_Eq (i + j) Em a =
    iter_Tm_upshift_Eq (j + i)
      (Logic.transport (λ x, iter x s m = itijsm) (Nat.add_comm i j) Em) a.
  Proof.
    apply iter_Tm_upshift_Eq_add_comm'.
  Qed.

  Lemma iter_Tm_upshift_Eq_add_assoc' {m itijksm : C} (i j k : nat)
    (Em : iter (i+(j+k)) s m = itijksm)
    (Em' : iter ((i+j)+k) s m = itijksm)
    (a : Tm m)
  : iter_Tm_upshift_Eq (i+(j+k)) Em a =
    iter_Tm_upshift_Eq ((i+j)+k) Em' a.
  Proof.
    revert Em Em'.
    rewrite Nat.add_assoc; intros.
    apply iter_Tm_upshift_Eq_UIP.
  Qed.
  Lemma iter_Tm_upshift_Eq_add_assoc_r {m itijksm : C} (i j k : nat)
    (Em : iter (i+(j+k)) s m = itijksm)
    (a : Tm m)
  : iter_Tm_upshift_Eq (i+(j+k)) Em a =
    iter_Tm_upshift_Eq ((i+j)+k)
      (Logic.transport (λ x, iter x s m = itijksm) (Nat.add_assoc i j k) Em)
      a.
  Proof.
    apply iter_Tm_upshift_Eq_add_assoc'.
  Qed.
  Lemma iter_Tm_upshift_Eq_add_assoc_l {m itijksm : C} (i j k : nat)
    (Em : iter ((i+j)+k) s m = itijksm)
    (a : Tm m)
  : iter_Tm_upshift_Eq ((i+j)+k) Em a =
    iter_Tm_upshift_Eq (i+(j+k))
      (Logic.transport (λ x, iter x s m = itijksm) (eq_sym (Nat.add_assoc i j k)) Em)
      a.
  Proof.
    erewrite <-iter_Tm_upshift_Eq_add_assoc'.
    reflexivity.
  Qed.

  Lemma iter_Tm_upshift_inj {m : ctx C} (i:nat)
    : injective (@iter_Tm_upshift _ m i).
  Proof.
    induction i.
    - apply Build_injective. auto.
    - apply Build_injective.
      intros a b H.
      apply IHi.
      simpl in H.
      refine (@inj _ _ _ _ _ (Up_tm_ntr_data_inj _) _ _ H).
  Qed.

  Lemma iter_Tm_upshift_Eq_inj {m itism : C} (i:nat)
    (E : iter i s m = itism)
    : injective (iter_Tm_upshift_Eq i E).
  Proof.
    revert m E;
    induction i; intros m E.
    - destruct E.
      unfold iter_Tm_upshift_Eq; simpl.
      apply Build_injective; auto.
    - destruct E.
      apply Build_injective.
      intros a b.
      intro H.
      erewrite !iter_Tm_upshift_Eq_swap in H.
      apply Up_tm_ntr_data_inj.
      eapply (IHi _ _).
      exact H.
      Unshelve.
        apply Nat.iter_swap.
  Qed.
 
  Lemma pi2_iter_upshift_Eq {m n itism itisn: C} (i:nat) (δ : m ~> s n)
    (Em : iter i s m = itism)
    (Esn : iter i s (s n) = s itisn)
    :  π2 (iter_upshift_Eq i Em Esn δ) ≈ (iter_Tm_upshift_Eq i Em (π2 δ)).
  Proof.
      
    destruct Em.
    simpl.
    rewrite <-pi2_iter_upshift.
    assert (E : iter i s n = itisn). {
      apply nnp_l_injective.
      specialize (f_equal nnp_l Esn).
      rewrite !nnp_l_iter, !nnp_l_s.
      lia.
    }
    destruct E.
    rewrite (UIP_ctx _ _ Esn (Nat.iter_swap i obj[C] s n)).
    reflexivity.
  Qed.

  Lemma transport_iter_Tm_upshift_Eq {m0 m itism: C} (i:nat) (a : Tm m)
  (Emi : iter i s m = itism)
  (Em0 : itism = m0)
  : Logic.transport (fobj[Tm]) Em0 (iter_Tm_upshift_Eq i Emi a) 
    ≈ iter_Tm_upshift_Eq i (eq_trans Emi Em0) a.
  Proof.
    apply eq_to_equiv.
    unfold iter_Tm_upshift_Eq.
    rewrite transport_trans.
    reflexivity.
  Qed.

End Iter_Tm_Upshift_withEq_properties.