From Stdlib Require Import Nat PeanoNat Arith Lia.

From Category Require Import Lib Theory
  Instance.Sets.

From CwFdeBruijn Require Import
  CatPsh Uwcwf
  Contextual
  Construction.FlippedComprehension
  Construction.Monoidification.SubstRel
  Structure.FlippedComprehension
  Structure.FlippedComprehension.IterUpshift
.

Section S_compose.

Context {C : UWCwFN}.

Definition Mndf_S_compose' (γ δ : Mndf_S_carrier) (l m n: C)
(rγ rδ : nat)
(Eγ : iter rγ s (Mndf_S_m γ) = m)
(Eγn : iter rγ s (Mndf_S_n γ) = n)
(Eδl : iter rδ s (Mndf_S_m δ) = l)
(Eδ : iter rδ s (Mndf_S_n δ) = m)
:= (Build_Mndf_S_carrier
  ( iter_upshift_Eq rγ Eγ Eγn (Mndf_S_rep γ)
  ∘ iter_upshift_Eq rδ Eδl Eδ (Mndf_S_rep δ))).

(* [Mndf_S_compose'] is independent of l, m, n, rδ, rγ, Eγ, Eγn, Eδl and Eδ *)
Lemma Mndf_S_compose'_rew (γ δ : Mndf_S_carrier)
  l m n rγ rδ Eγ Eγn Eδl Eδ 
  l' m' n' rγ' rδ' Eγ' Eγn' Eδl' Eδ' 
: Mndf_S_compose' γ δ l m n rγ rδ Eγ Eγn Eδl Eδ
  ≈ Mndf_S_compose' γ δ l' m' n' rγ' rδ' Eγ' Eγn' Eδl' Eδ'.
Proof.
  unfold Mndf_S_compose'.
  eapply (Build_Mndf_S_rel _ _ rγ' rγ).
  cbn [Mndf_S_rep].
  erewrite <-!iter_upshift_Eq_comp.
  rewrite <-!iter_upshift_Eq_add_fix_lhs.

  rewrite (iter_upshift_Eq_add_comm rγ' rγ).
  f_equiv.
  all: apply iter_upshift_Eq_rew'.
  Unshelve.

  all: simpl; try reflexivity.
  2-4: apply nnp_l_injective.
  all:
  specialize (f_equal nnp_l Eδl);
  specialize (f_equal nnp_l Eδ);
  specialize (f_equal nnp_l Eγ);
  specialize (f_equal nnp_l Eγn);
  specialize (f_equal nnp_l Eδl');
  specialize (f_equal nnp_l Eδ');
  specialize (f_equal nnp_l Eγ');
  specialize (f_equal nnp_l Eγn').
  all: rewrite !nnp_l_iter.
  all: lia.
Qed.

(* In [Mndf_S_compose'] you can replace δ for ↑^n δ *)
Lemma Mndf_S_compose'_upshift_Eq_r (γ δ : Mndf_S_carrier)
  (i:nat) itism Em itisn En l m n
  rγ rδ Eγ Eγn Eδl Eδ 
  rγ' rδ' Eγ' Eγn' Eδl' Eδ'
: Mndf_S_compose' γ δ l m n rγ rδ Eγ Eγn Eδl Eδ 
  ≈ Mndf_S_compose'
    γ  
    (Build_Mndf_S_carrier (@iter_upshift_Eq _ _ _ i itism Em itisn En (Mndf_S_rep δ)))
    (iter i s l) (iter i s m) (iter i s n) rγ' rδ' Eγ' Eγn' Eδl' Eδ'.
Proof.
  eapply (Build_Mndf_S_rel _ _ i 0).
  simpl; simpl in *.
  rewrite iter_upshift_Eq_beta_0.
  erewrite <-!iter_upshift_Eq_comp.
  erewrite <-!iter_upshift_Eq_add.
  erewrite iter_upshift_Eq_add_comm.
  f_equiv.
  - eapply iter_upshift_Eq_rew'.
    specialize (f_equal nnp_l Eγ); specialize (f_equal nnp_l Eγ').
    rewrite !nnp_l_iter. lia.
  - eapply iter_upshift_Eq_rew'.
    specialize (f_equal nnp_l Eδ); specialize (f_equal nnp_l Eδ').
    specialize (f_equal nnp_l En).
    rewrite !nnp_l_iter. lia.
  Unshelve.
    all: simpl.
    all: try reflexivity.
    all: apply (nnp_l_injective);
      specialize (f_equal nnp_l Eδl); specialize (f_equal nnp_l Eδl');
      specialize (f_equal nnp_l Eδ); specialize (f_equal nnp_l Eδ');
      specialize (f_equal nnp_l Eγ); specialize (f_equal nnp_l Eγ');
      specialize (f_equal nnp_l Eγn); specialize (f_equal nnp_l Eγn');
      specialize (f_equal nnp_l Em);
      rewrite !nnp_l_iter.
    all: try lia.
Qed.

(* Variant of [Mndf_S_compose'_upshift_Eq_r] with fixed parameters
to avoid irrelevant subgoal generation *)
Section Mndf_S_compose'_upshift_Eq_r_fixedargs.
  Context
  (γ δ : Mndf_S_carrier)
  (i : nat)
  (itism : obj[C])
  (Em : iter i s (Mndf_S_m δ) = itism)
  (itisn : obj[C])
  (En : iter i s (Mndf_S_n δ) = itisn)
  (l m n : obj[C])
  (rγ rδ : nat)
  (Eγ : iter rγ s (Mndf_S_m γ) = m)
  (Eγn : iter rγ s (Mndf_S_n γ) = n)
  (Eδl : iter rδ s (Mndf_S_m δ) = l)
  (Eδ : iter rδ s (Mndf_S_n δ) = m).


  Let Eγ' : iter (i + rγ) s (Mndf_S_m γ) = iter i s m.
  Proof.
    refine (eq_trans _ (f_equal (iter i s) Eγ)).
    now rewrite Nat.iter_add.
  Qed.
  Let Eγn' : iter (i + rγ) s (Mndf_S_n γ) = iter i s n.
  Proof.
    refine (eq_trans _ (f_equal (iter i s) Eγn)).
    now rewrite Nat.iter_add.
  Qed.
  Let Eδl' : iter rδ s itism = iter i s l.
  Proof.
    refine (eq_trans _ (f_equal (iter i s) Eδl)).
    now rewrite <-Nat.iter_add, Nat.add_comm, Nat.iter_add, Em.
  Qed.
  Let Eδ' : iter rδ s itisn = iter i s m.
  Proof.
    refine (eq_trans _ (f_equal (iter i s) Eδ)).
    now rewrite <-Nat.iter_add, Nat.add_comm, Nat.iter_add, En.
  Qed.

  Lemma Mndf_S_compose'_upshift_Eq_r_fixedargs
  : Mndf_S_compose' γ δ l m n rγ rδ Eγ Eγn Eδl Eδ
    ≈ Mndf_S_compose'
      γ  
      (Build_Mndf_S_carrier (@iter_upshift_Eq _ _ _ i itism Em itisn En (Mndf_S_rep δ)))
      (iter i s l) (iter i s m) (iter i s n) (i+rγ) rδ Eγ' Eγn' Eδl' Eδ'.
  Proof.
    apply Mndf_S_compose'_upshift_Eq_r.
  Qed.

End Mndf_S_compose'_upshift_Eq_r_fixedargs.


(* In [Mndf_S_compose'] you can replace γ for ↑^n γ *)
Lemma Mndf_S_compose'_upshift_Eq_l (γ δ : Mndf_S_carrier)
  (i:nat) itism Em itisn En l m n
  rγ rδ Eγ Eγn Eδl Eδ 
  rγ' rδ' Eγ' Eγn' Eδl' Eδ'
: Mndf_S_compose' γ δ l m n rγ rδ Eγ Eγn Eδl Eδ
  ≈ Mndf_S_compose'
    (Build_Mndf_S_carrier (@iter_upshift_Eq _ _ _ i itism Em itisn En (Mndf_S_rep γ)))
    δ
    (iter i s l) (iter i s m) (iter i s n) rγ' rδ' Eγ' Eγn' Eδl' Eδ'.
Proof.
  simpl in *.
  eapply (Build_Mndf_S_rel _ _ i 0).
  simpl; simpl in *.
  rewrite iter_upshift_Eq_beta_0.
  erewrite <-!iter_upshift_Eq_comp.
  erewrite <-!iter_upshift_Eq_add.
  erewrite iter_upshift_Eq_add_comm.
  f_equiv.
  - eapply iter_upshift_Eq_rew'.
    specialize (f_equal nnp_l Eγ);
      specialize (f_equal nnp_l Eγ');
      specialize (f_equal nnp_l Em).
    rewrite !nnp_l_iter. lia.
  - eapply iter_upshift_Eq_rew'.
    specialize (f_equal nnp_l Eδ); specialize (f_equal nnp_l Eδ').
    rewrite !nnp_l_iter. lia.
  Unshelve.
    all: simpl.
    all: try reflexivity.
    all: apply (nnp_l_injective);
      specialize (f_equal nnp_l Eδl); specialize (f_equal nnp_l Eδl');
      specialize (f_equal nnp_l Eδ); specialize (f_equal nnp_l Eδ');
      specialize (f_equal nnp_l Eδ); specialize (f_equal nnp_l Eδ');
      specialize (f_equal nnp_l Eγ); specialize (f_equal nnp_l Eγ');
      specialize (f_equal nnp_l Eγn); specialize (f_equal nnp_l Eγn');
      specialize (f_equal nnp_l Em);
      rewrite !nnp_l_iter.
    all: try lia.
Qed.

(*
  Variant of [Mndf_S_compose'_upshift_Eq_l]
  with fixed parameters to avoid irrelevant subgoal generation
*)
Section Mndf_S_compose'_upshift_Eq_l_fixedargs.
  Context
  (γ δ : Mndf_S_carrier)
  (i : nat)
  (itism : obj[C])
  (Em : iter i s (Mndf_S_m γ) = itism)
  (itisn : obj[C])
  (En : iter i s (Mndf_S_n γ) = itisn)
  (l m n : obj[C])
  (rγ rδ : nat)
  (Eγ : iter rγ s (Mndf_S_m γ) = m)
  (Eγn : iter rγ s (Mndf_S_n γ) = n)
  (Eδl : iter rδ s (Mndf_S_m δ) = l)
  (Eδ : iter rδ s (Mndf_S_n δ) = m).

  Let Eγ' : iter rγ s itism = iter i s m.
  Proof.
    refine (eq_trans _ (f_equal (iter i s) Eγ)).
    now rewrite <-Nat.iter_add, Nat.add_comm, Nat.iter_add, Em.
  Qed.
  Let Eγn' : iter rγ s itisn = iter i s n.
  Proof.
    refine (eq_trans _ (f_equal (iter i s) Eγn)).
    now rewrite <-Nat.iter_add, Nat.add_comm, Nat.iter_add, En.
  Qed.
  Let Eδl' : iter (i + rδ) s (Mndf_S_m δ) = iter i s l.
  Proof.
    refine (eq_trans _ (f_equal (iter i s) Eδl)).
    now rewrite <-Nat.iter_add, Nat.add_comm, Nat.iter_add.
  Qed.
  Let Eδ' : iter (i + rδ) s (Mndf_S_n δ) = iter i s m.
  Proof.
    refine (eq_trans _ (f_equal (iter i s) Eδ)).
    now rewrite <-Nat.iter_add.
  Qed.

  Lemma Mndf_S_compose'_upshift_Eq_l_fixedargs
  : Mndf_S_compose' γ δ l m n rγ rδ Eγ Eγn Eδl Eδ
    ≈ Mndf_S_compose'
      (Build_Mndf_S_carrier (@iter_upshift_Eq _ _ _ i itism Em itisn En (Mndf_S_rep γ)))
      δ
      (iter i s l) (iter i s m) (iter i s n) (rγ) (i+rδ) Eγ' Eγn' Eδl' Eδ'.
  Proof.
    apply Mndf_S_compose'_upshift_Eq_l.
  Qed.

End Mndf_S_compose'_upshift_Eq_l_fixedargs.

(* [Mndf_S_compose'] as a function of δ and γ, is a setoid morphism *)
Lemma Mndf_S_compose'_respects
  {γ γ0 δ δ0 : Mndf_S_carrier}
  {l m n rγ rδ Eγ Eγn Eδl Eδ}
  {l' m' n' rγ' rδ' Eγ' Eγn' Eδl' Eδ'}

  (eδ : δ ≈ δ0) (eγ : γ ≈ γ0)
  : Mndf_S_compose' γ δ l m n rγ rδ Eγ Eγn Eδl Eδ
  ≈ Mndf_S_compose' γ0 δ0 l' m' n' rγ' rδ' Eγ' Eγn' Eδl' Eδ'.
Proof.
  destruct eγ as [r1 r2 m1 n1 ? ? ? ? eγ].
  destruct eδ as [r3 r4 m2 n2 ? ? ? ? eδ].
  etransitivity.
  { unshelve eapply (Mndf_S_compose'_upshift_Eq_l_fixedargs _ _ r1 m1 _ n1).
    all: assumption. }
  etransitivity.
  { unshelve eapply (Mndf_S_compose'_upshift_Eq_r_fixedargs _ _ r3 m2 _ n2).
    all: assumption. }
  symmetry.
  etransitivity.
  { unshelve eapply (Mndf_S_compose'_upshift_Eq_l_fixedargs _ _ r2 m1 _ n1).
    all: assumption. }
  etransitivity.
  { unshelve eapply (Mndf_S_compose'_upshift_Eq_r_fixedargs _ _ r4 m2 _ n2).
    all: assumption. }
  etransitivity.
  { eapply (Mndf_S_compose'_rew _ _ _ _ _ _ _ _ _ _ _
      (iter r3 s (iter r1 s l))
      (iter r3 s (iter r1 s m))
      (iter r3 s (iter r1 s n))).
  }
  unfold Mndf_S_compose'.
  apply make_Mndf_S_rel_samectx.
  simpl.
  rewrite <-eγ.
  rewrite <-eδ.
  reflexivity.
Qed.

(* Composition in S is defined by fixing parameters in [Mndf_S_compose'] *)
Definition Mndf_S_compose : @Mndf_S_carrier C -> @Mndf_S_carrier C -> @Mndf_S_carrier C.
Proof.
  intros γ δ.
  exact (Mndf_S_compose' γ δ 
    _ (max_ctx (Mndf_S_n δ) (Mndf_S_m γ)) _
    (max_ctx_diff_r (Mndf_S_n δ) (Mndf_S_m γ))
    (max_ctx_diff_l (Mndf_S_n δ) (Mndf_S_m γ))
    (eq_sym (max_ctx_to_iter_r (Mndf_S_n δ) (Mndf_S_m γ)))
    eq_refl
    eq_refl
    (eq_sym (max_ctx_to_iter_l (Mndf_S_n δ) (Mndf_S_m γ))) ).
Defined.

#[global]
Instance Mndf_S_compose_respects :
  Proper (equiv ==> equiv ==> equiv)
    (@Mndf_S_compose).
Proof.
  intros ? ? ? ? ? ?.
  apply Mndf_S_compose'_respects; assumption.
Qed.

End S_compose.

Section S_compose_assoc.

  (*
       δ      γ      σ
    a ---> b ---> c ---> d
  *)

  Context {C : UWCwFN}.

  Lemma Mndf_S_compose'_assoc_0 (σ γ δ : @Mndf_S_carrier C)
    a b c d
    rσ rγ rδ  
    Eσc Eσd Eγb Eγc Eδa Eδb 

  : Mndf_S_compose' σ (Mndf_S_compose' γ δ a b c rγ rδ Eγb Eγc Eδa Eδb)
      a c d rσ 0 Eσc Eσd eq_refl eq_refl
  ≈ Mndf_S_compose' (Mndf_S_compose' σ γ b c d rσ rγ Eσc Eσd Eγb Eγc) δ
      a b d 0 rδ eq_refl eq_refl Eδa Eδb.
  Proof.
    unfold Mndf_S_compose'.

    apply make_Mndf_S_rel_samectx.
    simpl.
    rewrite comp_assoc.
    reflexivity.

    Unshelve.
    all: reflexivity.
  Qed. 

  Lemma Mndf_S_compose_matching_ctx {m n l : C } (γ : m ~> n) (δ : l ~> m)
    : Mndf_S_compose (Build_Mndf_S_carrier γ) (Build_Mndf_S_carrier δ) ≈ Build_Mndf_S_carrier (γ ∘ δ).
  Proof.
    unfold Mndf_S_compose.
    etransitivity.
    - unshelve eapply (Mndf_S_compose'_rew _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 0).
      all: simpl; try reflexivity.
    - reflexivity.
  Qed.

  Lemma Mndf_S_compose_assoc (σ γ δ : Mndf_S_carrier)
  : @Mndf_S_compose C σ (Mndf_S_compose γ δ) ≈ Mndf_S_compose (Mndf_S_compose σ γ) δ.
  Proof.
    set (rγ := max
                ((nnp_l (Mndf_S_n δ))-(nnp_l (Mndf_S_m γ)))
                ((nnp_l (Mndf_S_m σ))-(nnp_l (Mndf_S_n γ)))).
    set (rσ := (rγ + (nnp_l (Mndf_S_n γ))) - (nnp_l (Mndf_S_m σ))).
    set (rδ := (rγ + (nnp_l (Mndf_S_m γ))) - (nnp_l (Mndf_S_n δ))).
    
    assert (Eσγ :iter rσ s (Mndf_S_m σ) = iter rγ s (Mndf_S_n γ)).
    { unfold rσ, rδ, rγ.
      apply nnp_l_injective.
      rewrite !nnp_l_iter.
      lia. }
    assert (Eδγ : iter rδ s (Mndf_S_n δ) = iter rγ s (Mndf_S_m γ)).
    { unfold rσ, rδ, rγ.
      apply nnp_l_injective.
      rewrite !nnp_l_iter.
      lia. }

    rewrite 
      (Mndf_S_rel_iter_upshift γ rγ),
      (Mndf_S_rel_iter_upshift_Eq σ rσ Eσγ eq_refl),
      (Mndf_S_rel_iter_upshift_Eq δ rδ eq_refl Eδγ).

    rewrite !Mndf_S_compose_matching_ctx.
    apply make_Mndf_S_rel_samectx.
    cbn -[iter_upshift_Eq].
    rewrite comp_assoc.
    reflexivity.
  Qed.
End S_compose_assoc.

Section S_compose_id.

  Context {C : UWCwFN}.

  Definition Mndf_S_id' (n:C) : @Mndf_S_carrier C
    := Build_Mndf_S_carrier id[n].

  Definition Mndf_S_id : @Mndf_S_carrier C
    := Build_Mndf_S_carrier id[⋆_C].

  (* [S_compose_id] is independednt of [n] *)
  Lemma Mndf_S_id_rew_0 (n : C)
    : Mndf_S_id' n ≈ Mndf_S_id.
  Proof.
    induction n using UWCwFN_ind.
    { reflexivity. }
    - refine (transitivity _ IHn). 
      eapply (Build_Mndf_S_rel _ _ 0 1).
    erewrite iter_upshift_Eq_swap, !iter_upshift_Eq_beta_0.
    apply (symmetry upshift_id).
    Unshelve.
    all: reflexivity.
  Qed.

  Lemma Mndf_S_id_rew (n m : C)
    : Mndf_S_id' n ≈ Mndf_S_id' m.
  Proof.
    etransitivity.
    - apply Mndf_S_id_rew_0.
    - symmetry; apply Mndf_S_id_rew_0.
  Qed.

  (* Given a term of the ⋆_C context we can fully
  characterize [Mndf_S_id] equivalence class *)
  Section Mndf_S_id_to_id.
  Lemma Mndf_S_id_to_id {m} (a:Tm m) (δ : m ~> m)
    (E: Build_Mndf_S_carrier δ ≈ Mndf_S_id)  
  : δ ≈ id[m].
  Proof.
    etransitivity.
    - refine (Mndf_S_rel_to_iter_upshift _ E (i:=nnp_l m) _ _).
      2-3: abstract (apply nnp_l_injective; 
            rewrite nnp_l_iter; simpl; rewrite nnp_l_distobj; lia).
      exact a.
    - simpl.
      apply iter_upshift_Eq_id.
  Qed.

  Lemma Mndf_S_id_to_id_extctx {m} (δ : s m ~> s m)
    (E: Build_Mndf_S_carrier δ ≈ Mndf_S_id)  
  : δ ≈ id[s m].
  Proof.
    exact (Mndf_S_id_to_id (π2 id) _ E).
  Qed.
  End Mndf_S_id_to_id.

  Lemma Mndf_S_compose_id_left (δ : Mndf_S_carrier) 
    : Mndf_S_compose Mndf_S_id δ ≈ δ.
  Proof.
    destruct δ as [m n δ].
    rewrite <-(Mndf_S_id_rew_0 n).
    rewrite Mndf_S_compose_matching_ctx.
    apply make_Mndf_S_rel_samectx.
    simpl.
    rewrite id_left.
    reflexivity. 
  Qed.
  
  Lemma Mndf_S_compose_id_right (δ : Mndf_S_carrier) 
    : Mndf_S_compose δ Mndf_S_id ≈ δ.
  Proof.
    destruct δ as [m n δ].
    rewrite <-(Mndf_S_id_rew_0 m).
    rewrite Mndf_S_compose_matching_ctx.
    apply make_Mndf_S_rel_samectx.
    simpl.
    rewrite id_right.
    reflexivity. 
  Qed.

End S_compose_id.