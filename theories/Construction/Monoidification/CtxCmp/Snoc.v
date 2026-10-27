From Stdlib Require Import Nat PeanoNat Lia.

From Category Require Import Lib Theory
  Instance.Sets.

From CwFdeBruijn Require Import
  CatPsh Uwcwf
  Contextual

  Construction.Monoidification.SubstRel
  Construction.Monoidification.TmRel
  Construction.Monoidification.Compose
  Construction.Monoidification.Substitution
  
  Structure.FlippedComprehension
  Structure.FlippedComprehension.IterUpshift
  Structure.FlippedComprehension.IterTmUpshift
  Structure.FlippedComprehension.IterUpshiftSnoc.

Section Snoc.
Context {C : UWCwFN}.

Definition Mndf_snoc' (δ : Mndf_S_carrier) (a : Mndf_T_carrier) (m n: C)
(rδ ra : nat)
(Eδm : iter rδ s (Mndf_S_m δ) = m)
(Eδn : iter rδ s (Mndf_S_n δ) = n)
(Ea : iter ra s (Mndf_T_m a) = m)
:= Build_Mndf_S_carrier
    ⟨iter_upshift_Eq rδ Eδm Eδn (Mndf_S_rep δ),
      iter_Tm_upshift_Eq ra Ea (Mndf_T_rep a)⟩.

(* [Mndf_snoc'] is independent of m, n, rδ, ra, Eδm, Eδn, Ea *)
Lemma Mndf_snoc'_rew (δ : Mndf_S_carrier) (a : Mndf_T_carrier)
  m  n  rδ  ra  Eδm  Eδn  Ea 
  m' n' rδ' ra' Eδm' Eδn' Ea'
: Mndf_snoc' δ a m  n  rδ  ra  Eδm  Eδn  Ea 
≈ Mndf_snoc' δ a m' n' rδ' ra' Eδm' Eδn' Ea'.
Proof.
  unfold Mndf_snoc'.
  eapply (Build_Mndf_S_rel _ _ rδ' rδ).
  cbn [Mndf_S_rep].
  erewrite (iter_upshift_Eq_snoc _ _ _ _
    (iter_upshift_Eq rδ Eδm Eδn (Mndf_S_rep δ))
    (iter_Tm_upshift_Eq ra Ea (Mndf_T_rep a))).
  erewrite (iter_upshift_Eq_snoc _ _ _ _
    (iter_upshift_Eq rδ' Eδm' Eδn' (Mndf_S_rep δ))
    (iter_Tm_upshift_Eq ra' Ea' (Mndf_T_rep a))).
  
  erewrite <-!iter_upshift_Eq_add_fix_lhs.
  erewrite <-!iter_Tm_upshift_Eq_add.

  apply proper_snoc.
  1:rewrite (iter_upshift_Eq_add_comm rδ rδ');
    apply iter_upshift_Eq_rew'. 
  2:apply iter_Tm_upshift_Eq_rew'.
    Unshelve.
    all: simpl; try reflexivity.
    all: try apply nnp_l_injective;
      specialize (f_equal nnp_l Eδm);
      specialize (f_equal nnp_l Eδn);
      specialize (f_equal nnp_l Ea);
      specialize (f_equal nnp_l Ea');
      specialize (f_equal nnp_l Eδm');
      specialize (f_equal nnp_l Eδn');
      specialize (f_equal nnp_l Ea');
      repeat rewrite ?ctxext_to_s, ?nnp_l_iter, ?nnp_l_s ;
      lia.
Qed.

(* In [Mndf_snoc'] you can replace δ for ↑^n δ *)
Lemma Mndf_snoc'_upshift_Eq_l (δ : Mndf_S_carrier) (a : Mndf_T_carrier)
  (i:nat) itism Em itisn En m n
  rδ  ra  Eδm  Eδn  Ea
  rδ' ra' Eδm' Eδn' Ea' 
: Mndf_snoc' δ a m  n  rδ  ra  Eδm  Eδn  Ea 
≈ Mndf_snoc'
      (Build_Mndf_S_carrier (@iter_upshift_Eq _ _ _ i itism Em itisn En (Mndf_S_rep δ)))
      a
      (iter i s m) (iter i s n) rδ' ra' Eδm' Eδn' Ea'.
Proof.
  simpl in *.
  eapply (Build_Mndf_S_rel _ _ i 0).
  simpl; simpl in *.
  rewrite iter_upshift_Eq_beta_0.

  erewrite (iter_upshift_Eq_snoc _ _ _ _
    (iter_upshift_Eq rδ Eδm Eδn (Mndf_S_rep δ))
    (iter_Tm_upshift_Eq ra Ea (Mndf_T_rep a))).

  erewrite <-!iter_upshift_Eq_add.
  erewrite <-!iter_Tm_upshift_Eq_add.
  erewrite iter_upshift_Eq_add_comm.

  apply proper_snoc.
  1:apply iter_upshift_Eq_rew'. 
  2:apply iter_Tm_upshift_Eq_rew'.
  
  Unshelve.
    all: simpl; try reflexivity.
    all: try apply nnp_l_injective;
      specialize (f_equal nnp_l Em);
      specialize (f_equal nnp_l En);
      specialize (f_equal nnp_l Eδm);
      specialize (f_equal nnp_l Eδn);
      specialize (f_equal nnp_l Ea);
      specialize (f_equal nnp_l Ea');
      specialize (f_equal nnp_l Eδm');
      specialize (f_equal nnp_l Eδn');
      specialize (f_equal nnp_l Ea');
      repeat rewrite ?ctxext_to_s, ?nnp_l_iter, ?nnp_l_s ;
      try lia.
Qed.

(* Variant of [Mndf_snoc'_upshift_Eq_l] with fixed parameters
  to avoid irrelevant subgoal generation *)
Section Mndf_snoc'_upshift_Eq_l_fixedargs.
  Context
    (δ : Mndf_S_carrier)
    (a : Mndf_T_carrier)
    (i : nat)
    (itism : obj[C])
    (Em : iter i s (Mndf_S_m δ) = itism)
    (itisn : obj[C])
    (En : iter i s (Mndf_S_n δ) = itisn)
    (m n : obj[C])
    (rδ ra : nat)
    (Eδm : iter rδ s (Mndf_S_m δ) = m)
    (Eδn : iter rδ s (Mndf_S_n δ) = n)
    (Ea : iter ra s (Mndf_T_m a) = m).

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

  Let Ea' : iter (i+ra) s (Mndf_T_m a) = iter i s m.
  Proof.
    refine (eq_trans _ (f_equal (iter i s) Ea)).
    now rewrite Nat.iter_add.
  Qed.
  

  Lemma Mndf_snoc'_upshift_Eq_l_fixedargs
  : Mndf_snoc' δ a m  n  rδ  ra  Eδm  Eδn  Ea 
  ≈ Mndf_snoc'
      (Build_Mndf_S_carrier (@iter_upshift_Eq _ _ _ i itism Em itisn En (Mndf_S_rep δ)))
      a
      (iter i s m) (iter i s n) rδ (i+ra) Eδm' Eδn' Ea'.
  Proof.
    apply Mndf_snoc'_upshift_Eq_l.
  Qed.

End Mndf_snoc'_upshift_Eq_l_fixedargs.


(* In [Mndf_snoc'] you can replace a for ftm[Up]^n a *)
Lemma Mndf_snoc'_upshift_Eq_r (δ : Mndf_S_carrier) (a : Mndf_T_carrier)
  (i:nat) itism Em m n
  rδ  ra  Eδm  Eδn  Ea
  rδ' ra' Eδm' Eδn' Ea' 
: Mndf_snoc' δ a m  n  rδ  ra  Eδm  Eδn  Ea 
  ≈ Mndf_snoc'
    δ  
    (Build_Mndf_T_carrier (@iter_Tm_upshift_Eq _ _ i itism Em (Mndf_T_rep a)))
    (iter i s m) (iter i s n) ra' rδ' Ea' Eδn' Eδm'.
Proof.
  eapply (Build_Mndf_S_rel _ _ i 0).
  simpl; simpl in *.
  rewrite iter_upshift_Eq_beta_0.

  erewrite (iter_upshift_Eq_snoc _ _ _ _
    (iter_upshift_Eq rδ Eδm Eδn (Mndf_S_rep δ))
    (iter_Tm_upshift_Eq ra Ea (Mndf_T_rep a))).

  erewrite <-!iter_upshift_Eq_add.
  erewrite <-!iter_Tm_upshift_Eq_add.
  erewrite iter_upshift_Eq_add_comm.

  apply proper_snoc.
  1:apply iter_upshift_Eq_rew'. 
  2:apply iter_Tm_upshift_Eq_rew'.
  
  Unshelve.
    all: simpl; try reflexivity.
    all: try apply nnp_l_injective;
      specialize (f_equal nnp_l Em);
      specialize (f_equal nnp_l Eδm);
      specialize (f_equal nnp_l Eδn);
      specialize (f_equal nnp_l Ea);
      specialize (f_equal nnp_l Ea');
      specialize (f_equal nnp_l Eδm');
      specialize (f_equal nnp_l Eδn');
      specialize (f_equal nnp_l Ea');
      repeat rewrite ?ctxext_to_s, ?nnp_l_iter, ?nnp_l_s ;
      try lia.
Qed.

(* Variant of [Mndf_snoc'_upshift_Eq_l] with fixed parameters
to avoid irrelevant subgoal generation *)
Section Mndf_snoc'_upshift_Eq_r_fixedargs.
  Context
    (δ : Mndf_S_carrier)
    (a : Mndf_T_carrier)
    (i : nat)
    (itism : obj[C])
    (Em : iter i s (Mndf_T_m a) = itism)
    (m n : obj[C])
    (rδ ra : nat)
    (Eδm : iter rδ s (Mndf_S_m δ) = m)
    (Eδn : iter rδ s (Mndf_S_n δ) = n)
    (Ea : iter ra s (Mndf_T_m a) = m).

  Let Eδm'  : iter (i+rδ) s (Mndf_S_m δ) = iter i s m.
Proof. 
  refine (eq_trans _ (f_equal (iter i s) Eδm)).
  now rewrite <-Nat.iter_add.
Qed.
  Let Eδn' : iter (i+rδ) s (Mndf_S_n δ) = iter i s n.
Proof.
  refine (eq_trans _ (f_equal (iter i s) Eδn)).
  now rewrite <-Nat.iter_add.
Qed.
  Let Ea' : iter ra s itism = iter i s m.
Proof.
  refine (eq_trans _ (f_equal (iter i s) Ea)).
  now rewrite <-Nat.iter_add, Nat.add_comm, Nat.iter_add, Em.
Qed.

  Lemma Mndf_snoc'_upshift_Eq_r_fixedargs
  : Mndf_snoc' δ a m  n  rδ  ra  Eδm  Eδn  Ea 
  ≈ Mndf_snoc'
    δ
    (Build_Mndf_T_carrier (@iter_Tm_upshift_Eq _ _ i itism Em (Mndf_T_rep a)))
    (iter i s m) (iter i s n) (i+rδ) (ra) Eδm' Eδn' Ea'.
  Proof.  
    apply Mndf_snoc'_upshift_Eq_r.
  Qed.

End Mndf_snoc'_upshift_Eq_r_fixedargs.

(* [Mndf_snoc'] as a function of δ and a, is a setoid morphism *)
Lemma Mndf_snoc'_respects
  {δ δ0 : Mndf_S_carrier} {a a0 : Mndf_T_carrier}
  {m  n  rδ  ra  Eδm  Eδn  Ea}
  {m' n' rδ' ra' Eδm' Eδn' Ea'}
  (eδ : δ ≈ δ0) (ea : a ≈ a0)
  : Mndf_snoc' δ  a  m  n  rδ  ra  Eδm  Eδn  Ea
  ≈ Mndf_snoc' δ0 a0 m' n' rδ' ra' Eδm' Eδn' Ea'.
Proof.
  destruct eδ as [r1 r2 m1 n1 ? ? ? ? eδ].
  destruct ea as [r3 r4 n2 ? ? ea].
  etransitivity.
  { unshelve eapply (Mndf_snoc'_upshift_Eq_l_fixedargs _ _ r1 m1 _ n1).
    all: assumption. }
  etransitivity.
  { unshelve eapply (Mndf_snoc'_upshift_Eq_r_fixedargs _ _ r3 n2).
    all: assumption. }
  symmetry.
  etransitivity.
  { unshelve eapply (Mndf_snoc'_upshift_Eq_l_fixedargs _ _ r2 m1 _ n1).
    all: assumption. }
  etransitivity.
  { unshelve eapply (Mndf_snoc'_upshift_Eq_r_fixedargs _ _ r4 n2).
    all: assumption. }
  etransitivity.
  { eapply (Mndf_snoc'_rew _ _ _ _ _ _ _ _ _
      (iter r3 s (iter r1 s m))
      (iter r3 s (iter r1 s n))).
  }
  apply make_Mndf_S_rel_samectx.
  simpl.
  rewrite <-ea.
  rewrite <-eδ.
  reflexivity.
Qed.

(* snoc in S is defined by fixing parameters in [Mndf_snoc'] *)
Definition Mndf_snoc (δ : @Mndf_S_carrier C) (a : @Mndf_T_carrier C) : @Mndf_S_carrier C
  := Mndf_snoc' δ a
    (max_ctx (Mndf_S_m δ) (Mndf_T_m a)) _
    _ _
    (eq_sym (max_ctx_to_iter_l (Mndf_S_m δ) (Mndf_T_m a)))
    eq_refl
    (eq_sym (max_ctx_to_iter_r (Mndf_S_m δ) (Mndf_T_m a) )).

#[global]
Instance Mndf_snoc_respects :
  Proper (equiv ==> equiv ==> equiv)
    (@Mndf_snoc).
Proof.
  intros ? ? ? ? ? ?.
  apply Mndf_snoc'_respects; assumption.
Qed.

Definition Mndf_snoc_setoidmorphism
  : @SetoidMorphism ( (@Mndf_S_carrier C) * @Mndf_T_carrier C) _ (@Mndf_S_carrier C) _.
Proof.
  unshelve eapply Build_SetoidMorphism.
  - intros (δ,a). exact (Mndf_snoc δ a).
  - abstract (intros [? ?] [? ?] [e1 e2];
    rewrite e1, e2;
    reflexivity).
Defined.

Lemma Mndf_snoc_matching_ctx {m n : C} (δ : m ~> n) (a:Tm m)
  : Mndf_snoc (Build_Mndf_S_carrier δ) (Build_Mndf_T_carrier a)
  ≈ Build_Mndf_S_carrier ⟨δ,a⟩.
Proof.
  unfold Mndf_snoc.
  etransitivity.
  - unshelve eapply (Mndf_snoc'_rew _ _ _ _ _ _ _ _ _ _ _ 0 0).
    all: simpl; try reflexivity.
  - reflexivity.
Qed.


End Snoc.