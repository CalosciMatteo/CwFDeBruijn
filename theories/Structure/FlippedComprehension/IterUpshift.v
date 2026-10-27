From Stdlib Require Import Nat PeanoNat.
From Category Require Import Theory Lib.
From Category.Instance Require Import
  Sets.
From CwFdeBruijn Require Import 
  Lib.Transport Lib.Setoid
  CatPsh Uwcwf Structure.Uwcwf Structure.Uwcwf.Transport.
From CwFdeBruijn Require Import 
  Contextual
  Construction.FlippedComprehension
  Structure.FlippedComprehension
.

Open Scope nat.

Section Iter_Upshift.

Context {C : UWCwFN}.

Definition iter_upshift (i:nat)
  : forall {m n : C}, m ~> n -> iter i s m ~> iter i s n.
Proof.
  induction i.
  - intros ? ? δ. exact δ.
  - intros ? ? δ.
    exact (upshift (IHi m n δ)).
Defined.

#[global]
Instance proper_iter_upshift {i} {m n: C} : Proper (equiv ==> equiv) ( @iter_upshift i m n).
Proof.
  intros ? ? E.
  induction i; simpl.
  - proper.
  - f_equiv.
    apply IHi.
Qed.

Lemma iter_upshift_beta_S {m n : C} {i:nat} (δ : m ~> n)
  : iter_upshift (S i) δ = ↑ (iter_upshift i δ).
Proof.
  reflexivity.
Defined.


Lemma iter_upshift_swap' {m n : C} {i:nat}
(pm : iter i s (s m) = iter (S i) s m)
(pn : iter i s (s n) = iter (S i) s n)    
(δ : m ~> n)
: iter_upshift (S i) δ
= homcast pm pn (iter_upshift i (upshift δ)). 
Proof.
  simpl.
  induction i.
  - simpl.
    rewrite (UIP_refl_ctx pm), (UIP_refl_ctx pn).
    reflexivity.
  - simpl.
    erewrite <-upshift_transport.
    f_equal.
    apply IHi.
    Unshelve. all: apply Nat.iter_swap.
Qed.

Lemma iter_upshift_swap {m n : C} {i:nat}
  (δ : m ~> n)
  : iter_upshift (S i) δ
  = (Logic.transport (λ x , x ~> iter (S i) s n) (eq_sym (Nat.iter_succ_r i _ s m))
      (Logic.transport (λ x ,  iter i s (s m) ~> x) (eq_sym (Nat.iter_succ_r i _ s n))
        (iter_upshift i (upshift δ)))).
Proof. 
  apply iter_upshift_swap'.
Qed.

Lemma iter_upshift_comp {m' m n : C} (i:nat)
  (δ : m ~> n) (γ : m' ~> m)
  : (iter_upshift i δ) ∘ (iter_upshift i γ) ≈ iter_upshift i (δ ∘ γ).
Proof.
  induction i.
  - reflexivity.
  - simpl.
    rewrite <-upshift_comp.
    f_equiv.
    apply IHi.
Qed.

Lemma iter_upshift_id {m : C} (i:nat)
  : (iter_upshift i id[m]) ≈ id.
Proof.
  induction i.
  - reflexivity.
  - simpl.
    rewrite <-upshift_id.
    f_equiv.
    apply IHi.
Qed.

Lemma pi1_iter_upshift' {m n : C} (δ : m ~> s n) (i:nat)
  (E : iter i s (s n) = s (iter i s n))
  : π1 (Logic.transport (λ x, iter i s m ~> x) E (iter_upshift i δ)) ≈ iter_upshift i (π1 δ).
Proof.
  induction i.
  - rewrite (UIP_refl_ctx E).
    reflexivity.
  - simpl.
    erewrite <-IHi.
    rewrite <-pi1_upshift.
    f_equiv.
    change (Logic.transport (λ x, _ ~{ C }~> x) E (↑ (iter_upshift i δ)))
      with (homcast eq_refl E (↑ (iter_upshift i δ))).
    
    erewrite <-(upshift_transport (iter_upshift i δ) eq_refl eq_refl (Nat.iter_swap _ _ _ _)).
    f_equiv.
    simpl.
    reflexivity.
Qed.

Lemma pi1_iter_upshift {m n : C} (δ : m ~> s n) (i:nat)
  : π1 (Logic.transport (λ x, iter i s m ~> x) (Nat.iter_swap _ _ _ _) (iter_upshift i δ)) ≈ iter_upshift i (π1 δ).
Proof.
  apply pi1_iter_upshift'.
Qed.

End Iter_Upshift.

Section Iter_Upshift_withEq_def.

  Context {C : UWCwFN}.
  
  Definition iter_upshift_Eq {m n : C} (i:nat)
    {itism : C} (Em : iter i s m = itism)
    {itisn : C} (En : iter i s n = itisn)
    (δ : m ~> n)
  : itism ~> itisn
  := homcast Em En (iter_upshift i δ).
  #[global]
  Instance proper_iter_upshift_Eq {m n: C} (i:nat)
    {itism : C} (Em : iter i s m = itism)
    {itisn : C} (En : iter i s n = itisn)
  : Proper (equiv ==> equiv) ( @iter_upshift_Eq m n i itism Em itisn En).
  Proof.
    intros ? ? E.
    unfold iter_upshift_Eq.
    rewrite E.
    reflexivity.
  Qed.

  Definition iter_upshift_Eq_beta_0' {m n itism itisn : C}
    (Em : iter 0 s m = itism)
    (En : iter 0 s n = itisn)
    (δ : m ~> n)
  : iter_upshift_Eq 0 Em En δ = Logic.transport (λ x, x ~> itisn) Em 
    (Logic.transport (λ x, iter 0 s m ~> x) En (iter_upshift 0 δ)).
  Proof.
    reflexivity.
  Defined.

End Iter_Upshift_withEq_def.

Section Iter_Upshift_withEq_properties.
  Context {C : UWCwFN}.

  Lemma iter_upshift_Eq_beta_0 {m n: C}
    (Em : iter 0 s m = m)
    (En : iter 0 s n = n)
    (δ : m ~> n)
  : iter_upshift_Eq 0 Em En δ = δ.
  Proof.
    rewrite iter_upshift_Eq_beta_0'.
    rewrite (UIP_refl_ctx Em), (UIP_refl_ctx En).
    reflexivity.
  Qed.

  Lemma iter_upshift_Eq_beta_S_refl {m n itism itisn: C} (i:nat)
    (Em : iter (S i) s m = itism)
    (En : iter (S i) s n = itisn)
    (δ : m ~> n)
  : iter_upshift_Eq (S i) Em En δ
  = Logic.transport (λ x, x ~> itisn) Em 
      (Logic.transport (λ x, iter (S i) s m ~> x) En
        (upshift (iter_upshift_Eq i eq_refl eq_refl δ))). 
  Proof.
    reflexivity.
  Defined.

  Lemma iter_upshift_Eq_beta_S {m n itism itisn: C} (i:nat)
    (Em : iter i s m = itism) (Em' : iter (S i) s m = s itism)
    (En : iter i s n = itisn) (En' : iter (S i) s n = s itisn)
    (δ : m ~> n)
  : iter_upshift_Eq (S i) Em' En' δ = upshift (iter_upshift_Eq i Em En δ).
  Proof.
    unfold iter_upshift_Eq.
    erewrite upshift_transport.
    reflexivity.
  Qed.

  Lemma iter_upshift_swap_toEq {m n : C} {i:nat}
  (δ : m ~> n)
  : iter_upshift (S i) δ
  = iter_upshift_Eq i
      (eq_sym (Nat.iter_succ_r i _ s m)) (eq_sym (Nat.iter_succ_r i _ s n))
      (upshift δ).
  Proof.
    apply iter_upshift_swap.
  Qed.

  Section iter_upshift_Eq_swap.
  Lemma iter_upshift_Eq_swap {m n itism itisn: C} (i:nat)
    (Em : iter (S i) s m = itism) (Em' : iter i s (s m) = itism)
    (En : iter (S i) s n = itisn) (En' : iter i s (s n) = itisn)
    (δ : m ~> n)
  : iter_upshift_Eq (S i) Em En δ = (iter_upshift_Eq i Em' En' (upshift δ)).
  Proof.
    destruct Em, En.
    simpl.
    unfold iter_upshift_Eq.
    etransitivity.
    2:{ exact (iter_upshift_swap' Em' En' δ). }
    reflexivity.
  Qed.

  Section iter_upshift_Eq_swap_fix_rhs.

  Context {m n itism itisn: C} (i:nat)
    (Em : iter (S i) s m = itism)
    (En : iter (S i) s n = itisn)
    (δ : m ~> n).

  Let Em' : iter i s (s m) = itism.
  Proof. rewrite Nat.iter_swap; exact Em. Qed.
  Let En' : iter i s (s n) = itisn.
  Proof. rewrite Nat.iter_swap; exact En. Qed.

  Lemma iter_upshift_Eq_swap_fix_rhs
    : iter_upshift_Eq (S i) Em En δ = (iter_upshift_Eq i Em' En' (upshift δ)).
  Proof.
    apply iter_upshift_Eq_swap.
  Qed.

  End iter_upshift_Eq_swap_fix_rhs.
  End iter_upshift_Eq_swap.

  Lemma iter_upshift_Eq_to_iter_upshift {m n : C} (i:nat) (δ : m ~> n)
  : iter_upshift_Eq i eq_refl eq_refl δ = iter_upshift i δ.
  Proof.
    reflexivity.
  Defined.
  Lemma iter_upshift_Eq_to_iter_upshift' {m n : C} (i:nat) (δ : m ~> n)
  (Em : iter i s m = iter i s m)
  (En : iter i s n = iter i s n)
  : iter_upshift_Eq i Em En δ = iter_upshift i δ.
  Proof.
    rewrite (UIP_refl_ctx Em), (UIP_refl_ctx En).
    reflexivity.
  Qed.

  Lemma iter_upshift_Eq_UIP {m n itism itisn : C} (i:nat) (δ : m ~> n)
  (Em1 Em2 : iter i s m = itism)
  (En1 En2 : iter i s n = itisn)
  : iter_upshift_Eq i Em1 En1 δ = iter_upshift_Eq i Em2 En2 δ.
  Proof.
    rewrite (UIP_ctx _ _ Em1 Em2), (UIP_ctx _ _ En1 En2).
    reflexivity.
  Qed.

  Lemma iter_upshift_Eq_rew {m n itism itisn : C} (i j:nat) (δ : m ~> n)
  (p : i = j)
  (Eim : iter i s m = itism) (Ejm : iter j s m = itism)
  (Ein : iter i s n = itisn) (Ejn : iter j s n = itisn)
  : iter_upshift_Eq i Eim Ein δ = iter_upshift_Eq j Ejm Ejn δ.
  Proof.
    revert Eim Ejm Ein Ejn.
    rewrite p; intros.
    apply (iter_upshift_Eq_UIP _ _ _ _ _ _).
  Qed.

  Lemma iter_upshift_Eq_rew' {m n itism itisn : C} (i j:nat) (δ : m ~> n)
  (p : i = j)
  (Eim : iter i s m = itism) (Ejm : iter j s m = itism)
  (Ein : iter i s n = itisn) (Ejn : iter j s n = itisn)
  : iter_upshift_Eq i Eim Ein δ ≈ iter_upshift_Eq j Ejm Ejn δ.
  Proof.
    revert Eim Ejm Ein Ejn.
    rewrite p; intros.
    erewrite (iter_upshift_Eq_UIP _ _ _ _ _ _).
    reflexivity.
  Qed.

  Lemma iter_upshift_Eq_comp {m' m n itism' itism itisn : C} (i:nat)
    (Em' : iter i s m' = itism')
    (Em : iter i s m = itism)
    (En : iter i s n = itisn)
    (δ : m ~> n)
    (γ : m' ~> m)
  : (iter_upshift_Eq i Em En δ) ∘ (iter_upshift_Eq i Em' Em γ) ≈ iter_upshift_Eq i Em' En (δ ∘ γ).
  Proof.
    revert δ γ.
    destruct Em', Em, En.
    intros δ γ.
    apply iter_upshift_comp.
  Qed.

  Lemma iter_upshift_add {m n : C} (i j : nat)
    (E1 : iter i s (iter j s m) = iter (i + j) s m)
    (E2 : iter i s (iter j s n) = iter (i + j) s n)
    (δ : m ~> n)
  : iter_upshift (i + j) δ =
    iter_upshift_Eq i E1 E2 (iter_upshift j δ).
  Proof.
    revert i δ E1 E2.
    induction j; intros i δ E1 E2.
    - revert E1 E2; rewrite Nat.add_0_r; intros E1 E2.
      simpl.
      symmetry.
      rewrite <-iter_upshift_Eq_to_iter_upshift.
      apply iter_upshift_Eq_UIP.
    - revert E1 E2; rewrite Nat.add_succ_r; intros E1 E2.
      simpl.
      erewrite <-iter_upshift_Eq_swap.
      erewrite iter_upshift_Eq_beta_S.
      f_equal.
      apply IHj.
    Unshelve. all: simpl; rewrite Nat.iter_add; reflexivity.
  Qed.

  Lemma iter_upshift_Eq_add {m n itjsm itjsn itijsm itijsn : C} (i j : nat)
    (Em_j : iter j s m = itjsm)
    (En_j : iter j s n = itjsn)
    (Em_ij: iter (i + j) s m = itijsm)
    (En_ij: iter (i + j) s n = itijsn)
    (Em_i : iter i s itjsm = itijsm)
    (En_i : iter i s itjsn = itijsn)
    (δ : m ~> n)
  : iter_upshift_Eq (i + j) Em_ij En_ij δ =
    iter_upshift_Eq i Em_i En_i (iter_upshift_Eq j Em_j En_j δ).
  Proof.
    destruct Em_j, En_j, Em_ij, En_ij.
    simpl.
    apply iter_upshift_add.
  Qed.

  Section iter_upshift_Eq_add_fix_lhs.
    Context
      {m n itjsm itjsn itijsm itijsn : C} (i j : nat)
      (Em_j : iter j s m = itjsm)
      (En_j : iter j s n = itjsn)
      (Em_i : iter i s itjsm = itijsm)
      (En_i : iter i s itjsn = itijsn)
      (δ : m ~> n).

    Let Em_ij : iter (i + j) s m = itijsm.
    Proof. rewrite Nat.iter_add; now rewrite Em_j, Em_i. Qed.
    Let En_ij : iter (i + j) s n = itijsn.
    Proof. rewrite Nat.iter_add; now rewrite En_j, En_i. Qed.

    Lemma iter_upshift_Eq_add_fix_lhs
    : iter_upshift_Eq (i + j) Em_ij En_ij δ =
    iter_upshift_Eq i Em_i En_i (iter_upshift_Eq j Em_j En_j δ).
    Proof.
      apply iter_upshift_Eq_add.
    Qed.

  End iter_upshift_Eq_add_fix_lhs.

  Lemma iter_upshift_Eq_add_comm' {m n itijsm itijsn : C} (i j : nat)
    (Em : iter (i+j) s m = itijsm)
    (En : iter (i+j) s n = itijsn)
    (Em' : iter (j + i) s m = itijsm)
    (En' : iter (j + i) s n = itijsn)
    (δ : m ~> n)
  : iter_upshift_Eq (j + i) Em' En' δ =
    iter_upshift_Eq (i + j) Em En δ.
  Proof.
    revert Em En Em' En'.
    rewrite Nat.add_comm; intros.
    apply iter_upshift_Eq_UIP.
  Qed.

  Lemma iter_upshift_Eq_add_comm {m n itijsm itijsn : C} (i j : nat)
    (Em : iter (i+j) s m = itijsm)
    (En : iter (i+j) s n = itijsn)
    (δ : m ~> n)
  : iter_upshift_Eq (i + j) Em En δ =
    iter_upshift_Eq (j + i)
      (Logic.transport (λ x, iter x s m = itijsm) (Nat.add_comm i j) Em)
      (Logic.transport (λ x, iter x s n = itijsn) (Nat.add_comm i j) En) δ.
  Proof.
    apply iter_upshift_Eq_add_comm'.
  Qed.

  Lemma iter_upshift_Eq_add_assoc' {m n itijksm itijksn : C} (i j k : nat)
    (Em : iter (i+(j+k)) s m = itijksm)
    (En : iter (i+(j+k)) s n = itijksn)
    (Em' : iter ((i+j)+k) s m = itijksm)
    (En' : iter ((i+j)+k) s n = itijksn)
    (δ : m ~> n)
  : iter_upshift_Eq (i+(j+k)) Em En δ =
    iter_upshift_Eq ((i+j)+k) Em' En' δ.
  Proof.
    revert Em En Em' En'.
    rewrite Nat.add_assoc; intros.
    apply iter_upshift_Eq_UIP.
  Qed.
  Lemma iter_upshift_Eq_add_assoc_r {m n itijksm itijksn : C} (i j k : nat)
    (Em : iter (i+(j+k)) s m = itijksm)
    (En : iter (i+(j+k)) s n = itijksn)
    (δ : m ~> n)
  : iter_upshift_Eq (i+(j+k)) Em En δ =
    iter_upshift_Eq ((i+j)+k)
      (Logic.transport (λ x, iter x s m = itijksm) (Nat.add_assoc i j k) Em)
      (Logic.transport (λ x, iter x s n = itijksn) (Nat.add_assoc i j k) En)
      δ.
  Proof.
    apply iter_upshift_Eq_add_assoc'.
  Qed.
  Lemma iter_upshift_Eq_add_assoc_l {m n itijksm itijksn : C} (i j k : nat)
    (Em : iter ((i+j)+k) s m = itijksm)
    (En : iter ((i+j)+k) s n = itijksn)
    (δ : m ~> n)
  : iter_upshift_Eq ((i+j)+k) Em En δ =
    iter_upshift_Eq (i+(j+k))
      (Logic.transport (λ x, iter x s m = itijksm) (eq_sym (Nat.add_assoc i j k)) Em)
      (Logic.transport (λ x, iter x s n = itijksn) (eq_sym (Nat.add_assoc i j k)) En)
      δ.
  Proof.
    erewrite <-iter_upshift_Eq_add_assoc'.
    reflexivity.
  Qed.

  Definition iter_tm_upshift {m : ctx C} (i:nat) (a : Tm m) : Tm (iter i s m).
  Proof.
    induction i.
    - exact a.
    - exact (ftm[ Up ] IHi).
  Defined.
  
  Lemma iter_upshift_inj {m : ctx C} (n : ctx C) (i:nat) (a : Tm m)
    : injective (@iter_upshift _ i m n).
  Proof.
    induction i.
    - apply Build_injective. auto.
    - apply Build_injective.
      intros δ γ H.
      apply IHi.
      simpl in H.
      refine (@inj _ _ _ _ _ (upshift_inj _ _) _ _ H).
      apply (iter_tm_upshift i a).
  Qed.

  Lemma iter_upshift_inj_extsrc (m n : ctx C) (i:nat)
    : injective (@iter_upshift _ i (s m) n).
  Proof.
    apply Build_injective.
    intros δ ? E.
    unshelve eapply (inj E).
    apply iter_upshift_inj.
    apply (e1 id).
  Qed.

  Lemma iter_upshift_inj_exttgt (m n : ctx C) (i:nat)
    : injective (@iter_upshift _ i m (s n)).
  Proof.
    apply Build_injective.
    intros δ ? E.
    unshelve eapply (inj E).
    apply iter_upshift_inj.
    exact (e1 δ).
  Qed.

  Lemma iter_upshift_Eq_inj {m n itism itisn : C} (i:nat) (a:Tm m)
    (Em : iter i s m = itism)
    (En : iter i s n = itisn)
    : injective (iter_upshift_Eq i Em En).
  Proof.
    revert m n a Em En;
    induction i; intros m n a Em En.
    - destruct Em, En.
      unfold iter_upshift_Eq; simpl.
      apply Build_injective; auto.
    - destruct Em, En.
      apply Build_injective.
      intros δ γ.
      intro H.
      erewrite !iter_upshift_Eq_swap in H.
      apply upshift_inj.
      { exact a. }
      eapply (IHi _ _ _ _ _).
      exact H.
      Unshelve.
        all: try now rewrite Nat.iter_swap.
        exact (ftm[Up] a).
  Qed.

  Lemma iter_upshift_Eq_id {m itism : C} (i:nat)
    (Em En : iter i s m = itism)
    : iter_upshift_Eq i Em En id[m] ≈ id[itism].
  Proof.
    rewrite (iter_upshift_Eq_UIP i id _ Em _ Em).
    destruct Em.
    simpl.
    apply iter_upshift_id.
  Qed.
  
  Lemma pi1_iter_upshift_Eq {m n itism itisn: C} (i:nat) (δ : m ~> s n)
    (Em : iter i s m = itism)
    (Esn : iter i s (s n) = s itisn)
    (En : iter i s n = itisn)
    :  π1 (iter_upshift_Eq i Em Esn δ) ≈ (iter_upshift_Eq i Em En (π1 δ)).
  Proof.
    destruct Em.
    destruct En.
    apply (pi1_iter_upshift' _ _ Esn).
  Qed.

Lemma homcast_iter_upshift_Eq {m0 n0 m n itism itisn: C} (i:nat) (δ : m ~> n)
  (Emi : iter i s m = itism)
  (Eni : iter i s n = itisn)
  (Em0 : itism = m0)
  (En0 : itisn = n0)
  : Lib.Transport.homcast Em0 En0 (iter_upshift_Eq i Emi Eni δ) 
    ≈ iter_upshift_Eq i (eq_trans Emi Em0) (eq_trans Eni En0) δ.
Proof.
  apply eq_to_equiv.
  apply homcast_trans.
Qed.

End Iter_Upshift_withEq_properties.