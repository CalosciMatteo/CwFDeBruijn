From Stdlib Require Import Nat PeanoNat Arith Lia.

From Category Require Import Lib Theory
  Instance.Sets.

From CwFdeBruijn Require Import
  CatPsh Uwcwf
  Contextual
  Construction.FlippedComprehension
  Construction.Monoidification.SubstRel
  Construction.Monoidification.TmRel
  Construction.Monoidification.Compose
  Structure.FlippedComprehension
  Structure.FlippedComprehension.IterUpshift
  Structure.FlippedComprehension.IterTmUpshift
.

Section T_subst.

Context {C : UWCwFN}.

Definition Mndf_T_subst' (a : Mndf_T_carrier) (δ : Mndf_S_carrier) (m n: C)
  (ra rδ : nat)
  (Ea : iter ra s (Mndf_T_m a) = n)
  (Eδn : iter rδ s (Mndf_S_n δ) = n)
  (Eδm : iter rδ s (Mndf_S_m δ) = m)
  := Build_Mndf_T_carrier
      ((iter_Tm_upshift_Eq ra Ea (Mndf_T_rep a))
        [iter_upshift_Eq rδ Eδm Eδn (Mndf_S_rep δ)]).

(* [Mndf_T_subst'] is independent of m, n, ra, rδ, Ea, Eδn and Eδm *)
Lemma Mndf_T_subst'_rew (a : Mndf_T_carrier) (δ : Mndf_S_carrier)
  m n ra rδ Ea Eδn Eδm
  m' n' ra' rδ' Ea' Eδn' Eδm' 
: Mndf_T_subst' a δ m n ra rδ Ea Eδn Eδm
  ≈ Mndf_T_subst' a δ m' n' ra' rδ' Ea' Eδn' Eδm'.
Proof.
  unfold Mndf_T_subst'.
  eapply (Build_Mndf_T_rel _ _ rδ' rδ).
  cbn [Mndf_T_rep].
  erewrite <-!iter_Tm_upshift_Eq_subst.
  erewrite <-!iter_upshift_Eq_add.

  rewrite (iter_upshift_Eq_add_comm rδ rδ').
  f_equiv.

  erewrite <-!iter_Tm_upshift_Eq_add.
  apply iter_Tm_upshift_Eq_rew'.
  specialize (f_equal nnp_l Ea).
  specialize (f_equal nnp_l Eδn).
  specialize (f_equal nnp_l Ea').
  specialize (f_equal nnp_l Eδn').
  rewrite !nnp_l_iter.
  lia.
  Unshelve.
  all: simpl.
  all: try reflexivity.
  all: apply nnp_l_injective;
    specialize (f_equal nnp_l Ea);
    specialize (f_equal nnp_l Eδn);
    specialize (f_equal nnp_l Eδm);
    specialize (f_equal nnp_l Ea');
    specialize (f_equal nnp_l Eδn');
    specialize (f_equal nnp_l Eδm');
    rewrite !nnp_l_iter;
    lia.
Qed.

(* In [Mndf_T_subst'] you can replace δ for ↑^n δ *)
Lemma Mndf_T_subst'_upshift_Eq_r (a : Mndf_T_carrier) (δ : Mndf_S_carrier)
  (i:nat) itism Em itisn En m n
  ra rδ Ea Eδn Eδm
  ra' rδ' Ea' Eδn' Eδm'
: Mndf_T_subst' a δ m n ra rδ Ea Eδn Eδm
  ≈ Mndf_T_subst'
      a
      (Build_Mndf_S_carrier (@iter_upshift_Eq _ _ _ i itism Em itisn En (Mndf_S_rep δ)))
      (iter i s m) (iter i s n) ra' rδ' Ea' Eδn' Eδm'.
Proof.
  eapply (Build_Mndf_T_rel _ _ i 0).
  simpl; simpl in *.
  rewrite iter_Tm_upshift_Eq_beta_0.
  erewrite <-!iter_Tm_upshift_Eq_subst.
  erewrite <-!iter_upshift_Eq_add.
  erewrite iter_upshift_Eq_add_comm.
  f_equiv.
  
  - erewrite <-iter_Tm_upshift_Eq_add.
    eapply iter_Tm_upshift_Eq_rew'.
    specialize (f_equal nnp_l Ea); specialize (f_equal nnp_l Ea').
    rewrite !nnp_l_iter. lia.
  - eapply iter_upshift_Eq_rew'.
    specialize (f_equal nnp_l Eδn); specialize (f_equal nnp_l Eδn').
    specialize (f_equal nnp_l En).
    rewrite !nnp_l_iter. lia.
  Unshelve.
    all: simpl.
    all: try reflexivity.
    all: apply (nnp_l_injective);
      specialize (f_equal nnp_l Ea); specialize (f_equal nnp_l Ea');
      specialize (f_equal nnp_l Eδn); specialize (f_equal nnp_l Eδn');
      specialize (f_equal nnp_l Eδm); specialize (f_equal nnp_l Eδm');
      specialize (f_equal nnp_l Em);
      rewrite !nnp_l_iter.
    all: try lia.
Qed.

(* Variant of [Mndf_T_subst'_upshift_Eq_r] with fixed parameters
  to avoid irrelevant subgoal generation *)
Section Mndf_T_subst'_upshift_Eq_r_fixedargs.
  Context
    (a : Mndf_T_carrier)
    (δ : Mndf_S_carrier)
    (i : nat)
    (itism : obj[C])
    (Em : iter i s (Mndf_S_m δ) = itism)
    (itisn : obj[C])
    (En : iter i s (Mndf_S_n δ) = itisn)
    (m n : obj[C])
    (ra rδ : nat)
    (Ea : iter ra s (Mndf_T_m a) = n)
    (Eδn : iter rδ s (Mndf_S_n δ) = n)
    (Eδm : iter rδ s (Mndf_S_m δ) = m).

  Let Ea' : iter (i + ra) s (Mndf_T_m a) = iter i s n.
  Proof.
    refine (eq_trans _ (f_equal (iter i s) Ea)).
    now rewrite Nat.iter_add.
  Qed.
  Let Eδm' : iter rδ s itism = iter i s m.
  Proof.
    refine (eq_trans _ (f_equal (iter i s) Eδm)).
    now rewrite <-Nat.iter_add, Nat.add_comm, Nat.iter_add, Em.
  Qed.
  Let Eδn' : iter rδ s itisn = iter i s n.
  Proof.
    refine (eq_trans _ (f_equal (iter i s) Eδn)).
    now rewrite <-Nat.iter_add, Nat.add_comm, Nat.iter_add, En.
  Qed.

  Lemma Mndf_T_subst'_upshift_Eq_r_fixedargs
  : Mndf_T_subst' a δ m n ra rδ Ea Eδn Eδm
    ≈ Mndf_T_subst'
      a
      (Build_Mndf_S_carrier (@iter_upshift_Eq _ _ _ i itism Em itisn En (Mndf_S_rep δ)))
      (iter i s m) (iter i s n) (i+ra) rδ Ea' Eδn' Eδm'.
  Proof.
    apply Mndf_T_subst'_upshift_Eq_r.
  Qed.

End Mndf_T_subst'_upshift_Eq_r_fixedargs.


(* In [Mndf_T_subst'] you can replace a for ftm[Up]^n a *)
Lemma Mndf_T_subst'_upshift_Eq_l (a : Mndf_T_carrier) (δ : Mndf_S_carrier)
  (i:nat) itism Em m n
  ra rδ Ea Eδn Eδm
  ra' rδ' Ea' Eδn' Eδm'
: Mndf_T_subst' a δ m n ra rδ Ea Eδn Eδm
  ≈ Mndf_T_subst'
    (Build_Mndf_T_carrier (@iter_Tm_upshift_Eq _ _ i itism Em (Mndf_T_rep a)))
    δ
    (iter i s m) (iter i s n) ra' rδ' Ea' Eδn' Eδm'.
Proof.
  eapply (Build_Mndf_T_rel _ _ i 0).
  simpl; simpl in *.
  rewrite iter_Tm_upshift_Eq_beta_0.
  erewrite <-!iter_Tm_upshift_Eq_subst.
  erewrite <-!iter_upshift_Eq_add.
  erewrite <-!iter_Tm_upshift_Eq_add.
  erewrite iter_upshift_Eq_add_comm.
  f_equiv.
  - eapply iter_Tm_upshift_Eq_rew'.
    specialize (f_equal nnp_l Ea);
      specialize (f_equal nnp_l Ea');
      specialize (f_equal nnp_l Em).
    rewrite !nnp_l_iter. lia.
  - eapply iter_upshift_Eq_rew'.
    specialize (f_equal nnp_l Eδn); specialize (f_equal nnp_l Eδn').
    rewrite !nnp_l_iter. lia.
  Unshelve.
    all: simpl.
    all: try reflexivity.
    all: apply (nnp_l_injective);
      specialize (f_equal nnp_l Ea); specialize (f_equal nnp_l Ea');
      specialize (f_equal nnp_l Eδn); specialize (f_equal nnp_l Eδn');
      specialize (f_equal nnp_l Eδm); specialize (f_equal nnp_l Eδm');
      specialize (f_equal nnp_l Em);
      rewrite !nnp_l_iter.
    all: try lia.
Qed.

(* Variant of [Mndf_T_subst'_upshift_Eq_l]
  with fixed parameters to avoid irrelevant subgoal generation *)
Section Mndf_T_subst'_upshift_Eq_l_fixedargs.
  Context
    (a : Mndf_T_carrier)
    (δ : Mndf_S_carrier)
    (i : nat)
    (itism : obj[C])
    (Em : iter i s (Mndf_T_m a) = itism)
    (m n : obj[C])
    (ra rδ : nat)
    (Ea : iter ra s (Mndf_T_m a) = n)
    (Eδn : iter rδ s (Mndf_S_n δ) = n)
    (Eδm : iter rδ s (Mndf_S_m δ) = m).

  Let Ea' : iter ra s itism = iter i s n.
  Proof.
    refine (eq_trans _ (f_equal (iter i s) Ea)).
    now rewrite <-Nat.iter_add, Nat.add_comm, Nat.iter_add, Em.
  Qed.
  Let Eδm' : iter (i+rδ) s (Mndf_S_m δ) = iter i s m.
  Proof.
    refine (eq_trans _ (f_equal (iter i s) Eδm)).
    now rewrite Nat.iter_add.
  Qed.
  Let Eδn' : iter (i+rδ) s (Mndf_S_n δ) = iter i s n.
  Proof.
    refine (eq_trans _ (f_equal (iter i s) Eδn)).
    now rewrite Nat.iter_add.
  Qed.

  Lemma Mndf_T_subst'_upshift_Eq_l_fixedargs
  : Mndf_T_subst' a δ m n ra rδ Ea Eδn Eδm
    ≈ Mndf_T_subst'
      (Build_Mndf_T_carrier (@iter_Tm_upshift_Eq _ _ i itism Em (Mndf_T_rep a)))
      δ
      (iter i s m) (iter i s n) ra (i+rδ) Ea' Eδn' Eδm'.
  Proof.  
    apply Mndf_T_subst'_upshift_Eq_l.
  Qed.

End Mndf_T_subst'_upshift_Eq_l_fixedargs.

(* [Mndf_T_subst'] as a function of δ and γ, is a setoid morphism *)
Lemma Mndf_T_subst'_respects
  {a a0 : Mndf_T_carrier} {δ δ0 : Mndf_S_carrier}
  {m n ra rδ Ea Eδn Eδm}
  {m' n' ra' rδ' Ea' Eδn' Eδm'}

  (ea : a ≈ a0) (eδ : δ ≈ δ0)
  : Mndf_T_subst' a δ m n ra rδ Ea Eδn Eδm
  ≈ Mndf_T_subst' a0 δ0 m' n' ra' rδ' Ea' Eδn' Eδm'.
Proof.
  destruct ea as [r1 r2 n1 ? ? ea].
  destruct eδ as [r3 r4 m2 n2 ? ? ? ? eδ].
  etransitivity.
  { unshelve eapply (Mndf_T_subst'_upshift_Eq_l_fixedargs _ _ r1 n1).
    all: assumption. }
  etransitivity.
  { unshelve eapply (Mndf_T_subst'_upshift_Eq_r_fixedargs _ _ r3 m2 _ n2).
    all: assumption. }
  symmetry.
  etransitivity.
  { unshelve eapply (Mndf_T_subst'_upshift_Eq_l_fixedargs _ _ r2 n1).
    all: assumption. }
  etransitivity.
  { unshelve eapply (Mndf_T_subst'_upshift_Eq_r_fixedargs _ _ r4 m2 _ n2).
    all: assumption. }
  etransitivity.
  { eapply (Mndf_T_subst'_rew _ _ _ _ _ _ _ _ _
      (iter r3 s (iter r1 s m))
      (iter r3 s (iter r1 s n))).
  }
  unfold Mndf_T_subst'.
  simpl.
  apply make_Mndf_T_rel_samectx.
  simpl.
  rewrite <-ea.
  rewrite <-eδ.
  reflexivity.
Qed.

(* Substitution in T is defined by fixing parameters in [Mndf_T_subst'] *)
Definition Mndf_T_subst : @Mndf_T_carrier C -> @Mndf_S_carrier C -> @Mndf_T_carrier C.
Proof.
  intros a δ.
  exact (Mndf_T_subst' a δ 
    _ (max_ctx (Mndf_T_m a) (Mndf_S_n δ))
    (max_ctx_diff_l (Mndf_T_m a) (Mndf_S_n δ))
    (max_ctx_diff_r (Mndf_T_m a) (Mndf_S_n δ))
    (eq_sym (max_ctx_to_iter_l (Mndf_T_m a) (Mndf_S_n δ)))
    (eq_sym (max_ctx_to_iter_r (Mndf_T_m a) (Mndf_S_n δ)))
    eq_refl).
Defined.

#[global]
Instance Mndf_T_subst_respects :
  Proper (equiv ==> equiv ==> equiv)
    (@Mndf_T_subst).
Proof.
  intros ? ? ? ? ? ?.
  apply Mndf_T_subst'_respects; assumption.
Qed.

Program Definition Mndf_T_subst_SetoidMorphism (δ: Mndf_S_carrier) : SetoidMorphism (Mndf_T_SetoidObject) (Mndf_T_SetoidObject)
:= 
  {| morphism := λ a, Mndf_T_subst a δ|}.
Next Obligation.
  intros ? ? ?.
  apply Mndf_T_subst_respects.
  - assumption.
  - reflexivity.
Qed.

End T_subst.

Section T_subst_assoc.

  (*
       δ      γ   a
    l ---> m ---> n
  *)

  Context {C : UWCwFN}.

  Lemma Mndf_T_subst'_assoc_0 (a : @Mndf_T_carrier C) (γ δ : @Mndf_S_carrier C)
    l m n
    ra rγ rδ  
    Ean Eγm Eγn Eδl Eδm 

  : Mndf_T_subst' a (Mndf_S_compose' γ δ l m n rγ rδ Eγm Eγn Eδl Eδm)
      l n ra 0 Ean eq_refl eq_refl
  ≈ Mndf_T_subst' (Mndf_T_subst' a γ m n ra rγ Ean Eγn Eγm) δ
      l m 0 rδ eq_refl Eδm Eδl.
  Proof.
    unfold Mndf_T_subst', Mndf_S_compose'.

    apply make_Mndf_T_rel_samectx.
    simpl.
    rewrite substsubst.
    reflexivity.
  Qed. 

  Lemma Mndf_T_subst_matching_ctx {m n : C } (a : Tm n) (δ : m ~> n)
    : Mndf_T_subst (Build_Mndf_T_carrier a) (Build_Mndf_S_carrier δ) ≈ Build_Mndf_T_carrier (a[δ]).
  Proof.
    unfold Mndf_T_subst.
    etransitivity.
    - unshelve eapply (Mndf_T_subst'_rew _ _ _ _ _ _ _ _ _ _ _ 0 0).
      all: try reflexivity.
    - reflexivity.
  Qed.

  Lemma Mndf_T_subst_assoc (a : Mndf_T_carrier) (γ δ : Mndf_S_carrier)
  : @Mndf_T_subst C a (Mndf_S_compose γ δ) ≈ Mndf_T_subst (Mndf_T_subst a γ) δ.
  Proof.
    set (rγ := max
                ((nnp_l (Mndf_S_n δ))-(nnp_l (Mndf_S_m γ)))
                ((nnp_l (Mndf_T_m a))-(nnp_l (Mndf_S_n γ)))).
    set (ra := (rγ + (nnp_l (Mndf_S_n γ))) - (nnp_l (Mndf_T_m a))).
    set (rδ := (rγ + (nnp_l (Mndf_S_m γ))) - (nnp_l (Mndf_S_n δ))).
    
    assert (Eaγ :iter ra s (Mndf_T_m a) = iter rγ s (Mndf_S_n γ)).
    { unfold ra, rδ, rγ.
      apply nnp_l_injective.
      rewrite !nnp_l_iter.
      lia. }
    assert (Eδγ : iter rδ s (Mndf_S_n δ) = iter rγ s (Mndf_S_m γ)).
    { unfold ra, rδ, rγ.
      apply nnp_l_injective.
      rewrite !nnp_l_iter.
      lia. }
    rewrite 
      (Mndf_S_rel_iter_upshift γ rγ),
      (Mndf_T_rel_iter_upshift_Eq a ra Eaγ),
      (Mndf_S_rel_iter_upshift_Eq δ rδ eq_refl Eδγ).

    rewrite !Mndf_S_compose_matching_ctx.
    rewrite !Mndf_T_subst_matching_ctx.
    apply make_Mndf_T_rel_samectx.
    rewrite substsubst.
    reflexivity.
  Qed.
End T_subst_assoc.

Section T_subst_id.

  Context {C : UWCwFN}.

  Lemma Mndf_T_subst_id (a : Mndf_T_carrier) 
    : @Mndf_T_subst C a Mndf_S_id ≈ a.
  Proof.
    destruct a as [m a].
    rewrite <-(Mndf_S_id_rew_0 m).
    rewrite Mndf_T_subst_matching_ctx.
    apply make_Mndf_T_rel_samectx.
    simpl.
    apply substid. 
  Qed.

End T_subst_id.