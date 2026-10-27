From Stdlib Require Import Nat PeanoNat.
From Category Require Import Lib Theory.
From Category.Theory Require Import Morphisms.
From Category.Instance Require Import
  Sets Sets.Cartesian
  Fun Fun.Cartesian.
From Category.Construction Require Import Opposite.
From Category.Functor Require Import Product Hom Opposite.

From CwFdeBruijn Require Import
  Lib.Transport
  CatPsh Uwcwf
  Structure.Uwcwf Structure.Uwcwf.Iter
  Contextual FullSubCategory Construction.FlippedComprehension
  Structure.Uwcwf.Lift.

(* Lemmas involving standard and flipped comprehension *)
Section FlippedComprehension_properties.
  Context {C: UWCwFN}.

  Lemma e1pi1 {n m : C} (δ : m ~> s (s n))
  : (e1 (π1 δ)) ≈ e1 δ.
  Proof. now rewrite !e1_data_beta_s. Qed.
  Lemma pi2e2 {n m : C} (δ : m ~> s (s n))
  : (π2 (e2 δ)) ≈ π2 δ.
  Proof. now rewrite !e2_data_beta_s, pi2_snoc. Qed.

  Section e2id_epic.

    Lemma e2_id_comp {m n : C} (δ : n ~> m) (a:Tm(n)) : (e2 id) ∘ (cons (a,δ)) ≈ δ.
    Proof.
      rewrite e2_comp, id_left.
      apply e2_cons.
    Qed.

    Lemma e2id_epic {m:C} (a : Tm m) : Epic (e2 id[s m]).
    Proof.
      constructor; intros n δ γ H.
      rewrite <-(id_right δ), <-(id_right γ).
      rewrite <-(e2_id_comp id a).
      rewrite !comp_assoc, H.
      reflexivity.
    Qed.

    Lemma e2id_epic_ss {m:C} : Epic (e2 id[s (s m)]).
    Proof.
      apply (e2id_epic (π2 id)).
    Qed.
  End e2id_epic.
End FlippedComprehension_properties.

Section transport.
  Lemma e2_transport {C: UWCwFN} {m n n' :C} (δ : m ~> s n) (p : n = n')
    : e2 (Logic.transport (λ x , m ~> x) (f_equal s p) δ)
      = Logic.transport (λ x , m ~> x) p (e2 δ).
  Proof.
    destruct p.
    reflexivity.
  Qed.

  Lemma e1_transport {C: UWCwFN} {m n n' :C} (δ : m ~> s n) (p : n = n')
    : e1 (Logic.transport _(f_equal s p) δ)
      = Logic.transport _ p (e1 δ).
  Proof.
    destruct p.
    reflexivity.
  Qed.
End transport.

(* downshifted_identity *)
Notation "↓[ n ]" := (e2 id[s n]).

Section properties.

  Lemma lift_downid {C : UWCwFN} {n : C}
    : lift_on_sbs (↓[n]) ≈ ↓[s n].
  Proof.
    unfold lift_on_sbs.
    rewrite e2_data_beta_s.
    rewrite e2_comp, id_left.
    reflexivity.
  Qed.

  Lemma pi1_lift_e2 {C : UWCwFN} {n : C}: π1 (n:=n) (lift_on_sbs (e2 id)) ≈ e2 id ∘ π1 id.
  Proof.
    unfold lift_on_sbs.
    rewrite pi1_snoc.
    reflexivity.
  Qed.
  
  Lemma e2pi1 {C : UWCwFN} {m n : C} (δ : m ~> s (s n))
  : e2 (π1 δ) ≈ π1 (e2 δ).
  Proof.
    rewrite e2_data_beta_s.
    rewrite pi1_snoc.
    reflexivity.
  Qed.

  Lemma pi2iterpi1_to_e1 {C : UWCwFN} {m n : C} (δ : m ~> (s n))
    (E : s n = iter (nnp_l n) s (s (⋆_C)))
    : π2 (iter_π1_Eq (nnp_l n) E δ) ≈ e1 δ.
  Proof.
    induction n using UWCwFN_ind.
    - rewrite e1_data_beta_distobj.
      revert E. rewrite nnp_l_distobj. simpl. intro.
      rewrite iter_π1_Eq_beta_0.
      reflexivity.
    - rewrite e1_data_beta_s.
      etransitivity.
      2:{ apply (IHn (π1 δ)). }
      f_equiv.
      clear IHn.
      revert E; rewrite nnp_l_s; intro E.
      erewrite iter_pi1_Eq_beta_S.
      reflexivity.
      Unshelve.
      rewrite Nat.iter_swap.
      f_equal.
      symmetry.
      apply nnp_cl.
  Qed.

  Lemma iter_π1_downid {C : UWCwFN} (n:nat)
  : iter_π1 n (↓[ctl_c n]) ≈ iter_π1 (S n) id{C}.
  Proof.
    induction n.
    - now rewrite e2_data_beta_distobj.
    - rewrite iter_pi1_beta_S.
      change (ctl_c (S n)) with (s (C:= C) (ctl_c n)).
      rewrite <- lift_downid.
      unfold lift_on_sbs; rewrite pi1_snoc.
      rewrite <-iter_pi1_comp.
      rewrite IHn.
      rewrite iter_pi1_comp, id_left.
      reflexivity.
  Qed.

  Lemma iter_π1_downid' {C : UWCwFN} (n:nat)
  : iter_π1 n (↓[iter n s (⋆_ C)]) ≈ iter_π1 (S n) id{C}.
  Proof.
    apply iter_π1_downid.
  Qed.

  Lemma pi2_iter_pi1_e2''' {C : UWCwFN} {m n: C}
    (j:nat) (δ : m ~> s (iter j s (s n)))
    (E : s (iter j s (s n)) = iter j s (s (s n)))
  : π2 (iter_π1 j (e2 δ)) ≈ π2 (iter_π1_Eq j E δ).
  Proof.
    induction j.
    - rewrite iter_π1_Eq_beta_0.
      simpl.
      rewrite pi2e2.
      reflexivity.
    - unshelve erewrite iter_pi1_Eq_beta_S.
      { now rewrite !Nat.iter_swap. }
      rewrite iter_pi1_beta_S.
      rewrite <-e2pi1.
      apply (IHj (π1 δ) _).
  Qed.

  Lemma pi2_iter_pi1_Eq_e2'' {C : UWCwFN} {m n: C}
    (j:nat) (δ : m ~> s (iter j s (s n)))
    (E : iter j s (s n) = iter j s (s n))
    (E' : s (iter j s (s n)) = iter j s (s (s n)))
  : π2 (iter_π1_Eq j E (e2 δ)) ≈ π2 (iter_π1_Eq j E' δ).
  Proof.
    rewrite (UIP_refl_ctx E).
    apply pi2_iter_pi1_e2'''.
  Qed.

  Lemma pi2_iter_pi1_Eq_e2 {C : UWCwFN} {m n jn: C}
    (j:nat) (δ : m ~> s (s jn))
    (E : s jn = iter j s (s n))
    (E' : s (s jn) = iter j s (s (s n)))
  : π2 (iter_π1_Eq j E (e2 δ)) ≈ π2 (iter_π1_Eq j E' δ).
  Proof.
    remember E. clear Heqe.
    revert e E' δ.
    rewrite !E; intros e E' δ.
    apply pi2_iter_pi1_Eq_e2''.
  Qed.

  Lemma pi2_iter_pi1_downid {C : UWCwFN} (j:nat) {n n': C}
    (E: (s n) = iter j s (s n'))
    (E': s (s n) = iter j s (s (s n')))
    : π2 (iter_π1_Eq j E ↓[s n]) ≈ π2 (iter_π1_Eq j E' id).
  Proof.
    apply pi2_iter_pi1_Eq_e2.
  Qed.

  Section variants_ft_one_Eq.
    Context {C : UWCwFN} (j:nat) {n jn:C} (E0 : jn = iter j s n).
    Let E' := (eq_trans (f_equal s E0) (eq_sym (Nat.iter_swap _ _ s _))).
    Let E'' := (eq_trans (f_equal s E') (eq_sym (Nat.iter_swap _ _ s _))).

    Lemma pi2_iter_pi1_Eq_e2' {m: C} (δ : m ~> s (s jn))
      (E : s jn = iter j s (s n))
    : π2 (iter_π1_Eq j E' (e2 δ)) ≈ π2 (iter_π1_Eq j E'' δ).
    Proof.
      apply pi2_iter_pi1_Eq_e2.
    Qed.
    Lemma pi2_iter_pi1_downid'
      : π2 (iter_π1_Eq j E' ↓[s jn]) ≈ π2 (iter_π1_Eq j E'' id).
    Proof.
      apply pi2_iter_pi1_Eq_e2.
    Qed.
  End variants_ft_one_Eq.

End properties.

Section upshift.

  Context {C : UWCwFN}.

  Context {m n : C} (δ : m ~> n).

  Let E : s m = iter (nnp_l m) s (s (⋆_C)).
  Proof.
    symmetry.
    rewrite (Nat.iter_swap (nnp_l m) _ s (⋆_C)).
    f_equal.
    apply nnp_cl.
  Defined.

  Definition upshift : (s m ~> s n)
  := (cons(π2(iter_π1_Eq (nnp_l m) E id),(δ∘↓[m]))).
    

End upshift.

#[global]
Instance proper_upshift {C : UWCwFN} {m n : C}
  : (Proper (equiv ==> equiv) (@upshift C m n)).
Proof.
  intros ? ? E.
  unfold upshift.
  rewrite E.
  reflexivity.
Qed.

Notation "'↑'" := upshift.

Section upshift_properties.
  Context {C : UWCwFN}.

  Lemma e1_upshift {m n : C} (δ : m ~> n)
  (E : s m = iter (nnp_l m) s (s (⋆_C)))
  : e1 (↑δ) ≈ π2(iter_π1_Eq (nnp_l m) E id).
  Proof.
    unfold upshift.
    rewrite e1_cons.
    repeat f_equiv.
    apply UIP_ctx.
  Qed.

  Lemma upshift_s {m n : C} (δ : m ~> s n)
  : ↑ δ ≈ ⟨↑ (π1 δ),π2 (δ∘↓[m])⟩.
  Proof.
    unfold upshift at 1.
    rewrite cons_data_beta_s.
    f_equiv.
    unfold upshift.
    rewrite pi1_comp.
    reflexivity.
  Qed.

  Lemma upshift_snoc {m n : C} (δ : m ~> n) (a: Tm m)
    : ↑⟨δ,a⟩ ≈ ⟨↑δ, a[↓[m]]⟩.
  Proof.
    unfold upshift at 1.
    rewrite snoc_comp.
    rewrite cons_data_beta_s, pi2_snoc, pi1_snoc.
    simpl.
    reflexivity.
  Qed.

  Lemma upshift_iterpi1_id {i:nat} {n m:C}
    (E1 : m = iter i s n)
    (E2 : s m = iter i s (s n))
    : ↑ (iter_π1_Eq i E1 id{C})
    ≈ iter_π1_Eq i E2 id.
  Proof.
    revert i E1 E2.
    induction n using UWCwFN_ind; intros i E1 E2.
    - unfold upshift.
      rewrite cons_data_beta_0.
      rewrite iter_pi1_Eq_comp, id_left.
      revert E2. rewrite E1.
      rewrite !iter_π1_Eq_to_iter_π1.
      intro E2.
      rewrite  iter_π1_downid'.
      erewrite iter_π1_swap_toEq.
      erewrite (iter_pi1_Eq_rew (nnp_l _) i).
      2:{ now rewrite nnp_l_iter, nnp_l_distobj. }
      rewrite <-snoc_eta.
      f_equiv.
      apply UIP_ctx.
    - induction m using UWCwFN_ind.
      { exfalso.
        rewrite Nat.iter_swap in E1.
        apply (f_equal nnp_l) in E1.
        rewrite nnp_l_distobj, nnp_l_s in E1.
        refine (Nat.neq_0_succ _ E1). }
      specialize (IHn (S i)).
      unfold upshift.
      rewrite cons_data_beta_s.
      rewrite iter_pi1_Eq_comp, id_left.
      eapply (Equivalence_Transitive _ ⟨_,_⟩).
      { apply proper_snoc.
        2:{ reflexivity. }
        Unshelve. 2:{
          refine (↑ (iter_π1_Eq (S i) _ id)).
          simpl.
          rewrite <-Nat.iter_swap.
          exact E1.
          }
        unfold upshift.
        rewrite iter_pi1_Eq_comp, id_left.
        erewrite iter_pi1_Eq_swap.
        reflexivity. }
      unshelve erewrite IHn.
      { simpl.
        f_equal.
        exact E1.  }
      erewrite iter_pi1_Eq_swap.
      rewrite pi2_iter_pi1_downid.
      rewrite <-snoc_eta.
      reflexivity.
  Qed.

  Section variants_ft_one_Eq.
  Context {i:nat} {n jn:C} (E0 : jn = iter i s n).
  Let E' := (eq_trans (f_equal s E0) (eq_sym (Nat.iter_swap _ _ s _))).
    

  Lemma upshift_iterpi1_id'
    : ↑ (iter_π1_Eq i E0 id{C}) ≈ iter_π1_Eq i E' id.
  Proof.
    apply upshift_iterpi1_id.
  Qed.

  End variants_ft_one_Eq.

  Lemma upshift_id {n:C}
  : ↑ id[n] ≈ id[s n].
  Proof.
    assert (H := @upshift_iterpi1_id' 0 n n eq_refl).
    rewrite !iter_π1_Eq_beta_0 in H.
    exact H.
  Qed.

  Lemma upshift_naturality {m n : C} (δ : m ~> n)
  : ↓[n]∘ ↑δ ≈ δ ∘ ↓[m].
  Proof.
    induction n using UWCwFN_ind.
    - unfold upshift.
      rewrite e2_data_beta_distobj, cons_data_beta_distobj, pi1_id_comp_snoc.
      reflexivity.
    - rewrite <-lift_downid.
      unfold lift_on_sbs.
      rewrite snoc_comp, pi2_subst, id_left.
      rewrite <-comp_assoc.
      rewrite pi1_comp, id_left.
      rewrite upshift_s.
      rewrite pi1_snoc, pi2_snoc.
      rewrite (IHn (π1 δ)), pi1_comp, <-snoc_eta.
      reflexivity.
  Qed.

  Lemma Tm_upshift_subst {m n : C} (δ : m ~> n) (a : Tm n)
  : (a[δ])[↓[m]] ≈ (a[↓[n]])[↑δ].
  Proof.
    rewrite !substsubst.
    rewrite <-upshift_naturality.
    reflexivity.
  Qed.

  Lemma upshift_comp {m' m n : C} (γ : m' ~> m) (δ : m ~> n)
  : ↑(δ∘γ) ≈ ↑δ ∘ ↑γ.
  Proof.
    unfold upshift at 2.
    rewrite cons_comp.
    rewrite pi2iterpi1_to_e1.

    rewrite e1_subst, id_left.
    rewrite e1_upshift.
    rewrite <-comp_assoc, upshift_naturality, comp_assoc.
    unfold upshift.
    reflexivity.
  Qed.

  Lemma pi1_upshift {m n : C} (δ : m~>s n)
    : π1 (↑ δ) ≈ ↑ (π1 δ).
  Proof.
    unfold upshift at 1.
    rewrite cons_data_beta_s, pi1_snoc.
    rewrite <-pi1_comp.
    reflexivity.
  Qed.

  Lemma pi2_upshift {m n : C} (δ : m~>s n)
    : π2 (↑ δ) ≈ (π2 δ)[  ↓[m]].
  Proof.
    unfold upshift at 1.
    rewrite cons_data_beta_s, pi2_snoc.
    rewrite <-pi2_subst.
    reflexivity.
  Qed.

  Section upshift_inj.
    Lemma upshift_inj {m : ctx C} (n : ctx C) (a : Tm m)
      : injective (@upshift _ m n).
    Proof.
      apply Build_injective.
      intros δ γ E.
      assert (EE := proper_morphism {| morphism := e2; |} _ _ E).
      simpl in EE.
      unfold upshift in EE.
      rewrite !e2_cons in EE.
      apply (e2id_epic a).
      exact EE.
    Qed.

    Lemma upshift_inj_exttgt (m n : ctx C) : injective (@upshift _ m (s n)).
    Proof.
      apply Build_injective.
      intros δ ? E.
      unshelve eapply (inj E).
      apply upshift_inj.
      exact (e1 δ).
    Qed.

    Lemma upshift_inj_extsrc (m n : ctx C) : injective (@upshift _ (s m) n).
    Proof.
      apply Build_injective.
      intros δ ? E.
      unshelve eapply (inj E).
      apply upshift_inj.
      apply (e1 id).
    Qed.
  End upshift_inj.
End upshift_properties.

Section upshift_functor.

  Context {C : UWCwFN}.

  Program Definition Up_ctx_fnc : C ⟶ C := {|
    fobj := s;
    fmap := (λ Γ Δ, ↑);
    
    fmap_id := (λ _, upshift_id);
    fmap_comp := (λ x y z δ γ, upshift_comp γ δ)
  |}.

  Definition Up_tm_ntr_data (n:C) (a : Tm n) : Tm (s n)
    := a [↓[n]].
  #[global] Instance proper_Up_tm_ntr_data
    {n : C} : (Proper (equiv ==> equiv) (Up_tm_ntr_data n)).
  Proof.
    unfold Up_tm_ntr_data.
    proper.
    rewrite X.
    reflexivity.
  Qed.

  Program Definition Up_tm_ntr : Tm ⟹ Tm ◯ Up_ctx_fnc^op :=
  @Build_Transform' _ _ Tm (Tm ◯ Up_ctx_fnc^op)
    (λ n , {| morphism := Up_tm_ntr_data n; |}
      : Tm n ~{ Sets }~> Tm (s n ))
    _.
  Next Obligation.
    change ((x0 [↓[ x]])[↑f] ≈ (x0[f])[↓[y]]).
    rewrite !substsubst.
    f_equiv.
    apply upshift_naturality.
  Qed.

  Definition Up : C ~{CwPs}~> C := {|
    ctx_fnc := Up_ctx_fnc;
    tm_ntr := Up_tm_ntr
  |}.

  Section Up_tm_ntr_data_inj.
    Context (n:C).

    Lemma Up_tm_ntr_data_inj : injective (Up_tm_ntr_data n).
    Proof.
      apply Build_injective.
      intros a b E.
      unshelve eassert (EE := proper_morphism {| morphism := λ x, ⟨id∘↓[n],x⟩; |} _ _ E).
      { proper. }
      { intros ? ? ?.
        f_equiv.
        assumption. }
      simpl in EE.
      unfold Up_tm_ntr_data in EE.
      rewrite <-!snoc_comp in EE.
      unshelve eapply (epic _ _ _) in EE.
      - apply e2id_epic.
        exact a.
      - apply (proper_morphism {| morphism := π2; |} _ _) in EE.
        simpl in EE.
        rewrite !pi2_snoc in EE.
        exact EE.
    Qed.
  End Up_tm_ntr_data_inj.

End upshift_functor.

Lemma Tm_upshift_transport {C : UWCwFN} {m m' : C} (a : Tm m)
    (pm : m = m') (spm : s m = s m') 
    : ftm[ Up ] (Logic.transport (λ x , Tm x) pm a)
      = Logic.transport (λ x , Tm x) spm (ftm[ Up ] a).
Proof.
  rewrite (UIP_ctx _ _ spm (f_equal s pm)).
  destruct pm.
  reflexivity.
Qed.

Lemma upshift_transport {C : UWCwFN} {m m' n n' : C} (δ : m ~> n)
  (pm : m = m') (spm : s m = s m') 
  (pn : n = n') (spn : s n = s n') 
  : upshift (homcast pm pn δ)
    = homcast spm spn (upshift δ).
Proof.
  rewrite (UIP_ctx _ _ spm (f_equal s pm)).
  rewrite (UIP_ctx _ _ spn (f_equal s pn)).
  destruct pm, pn.
  reflexivity.
Qed.