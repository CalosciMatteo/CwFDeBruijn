From Stdlib Require Import ssrfun Nat PeanoNat Lia.
From Category Require Import Lib Theory.

From Category Require Import Instance.Sets.
From Category Require Import Construction.Subcategory.
From CwFdeBruijn Require Import Lib.Transport CatPsh Uwcwf Structure.Uwcwf FullSubCategory.

Section definitions.

  Context {C : UWCwF}.
  (* Pre-Contextuality : any context can be obtained as an extension chain *)
  Class PreContextual : Type := { 
    ctl_l : ctx C -> nat;
    ctl_cl : cancel ctl_l ctl_c;
  }.

  (* Contextuality or NNP (Natural Number Property) :
  any context can be obtained in an unique way as an extension chain
  i.e. context are in bijection with natural numbers *)
  Class NaturalNumberProperty : Type := {
    nnp_l : ctx C -> nat;
    nnp_cl' : cancel nnp_l ctl_c;
    nnp_lc : cancel ctl_c nnp_l
  }.

  (* This is the construction in Th. 4.2.3 of the HoTT book *)
  Definition nnp_cl {NNP : NaturalNumberProperty} : cancel nnp_l ctl_c.
  Proof.
    intro x.
    refine (eq_trans _ (eq_trans _ _)).
    - symmetry.
      exact (nnp_cl' _).
    - apply (f_equal ctl_c).
      exact (nnp_lc _).
    - exact (nnp_cl' _).
  Defined.
End definitions.

Definition cUWCwF := { uwcwf : UWCwF & @PreContextual uwcwf }.
Definition cUWCwF_incl : cUWCwF -> UWCwF
  := @projT1 UWCwF (@PreContextual).
Coercion cUWCwF_incl : cUWCwF >-> UWCwF.
Instance cUWCwF_PreContextual (C : cUWCwF) : @PreContextual C
  := projT2 C.

Definition UWCwFN := { uwcwf : UWCwF & @NaturalNumberProperty uwcwf }.
Definition UWCwFN_incl : UWCwFN -> UWCwF
  := @projT1 UWCwF (@NaturalNumberProperty).
Coercion UWCwFN_incl : UWCwFN >-> UWCwF.
Instance cUWCwF_NNP (C : UWCwFN) : @NaturalNumberProperty C
  := projT2 C.

Arguments PreContextual _ : clear implicits.
Arguments NaturalNumberProperty _ : clear implicits.
Arguments ctl_cl {_ _}.

Definition cUWCwFs : Category := Sub _ (make_FullSubCategory UWCwFs PreContextual).

Definition UWCwFNs : Category := Sub _ (make_FullSubCategory UWCwFs NaturalNumberProperty).


Section UWCwFN_accessor.

  #[export]
  Instance Incl_Pred_UWCwF_N (C : UWCwFN)
    : NaturalNumberProperty ( C)
    := Incl_Pred (make_FullSubCategory UWCwFs NaturalNumberProperty) C.

End UWCwFN_accessor.

Section UWCwFN_properties.
  Context {C : UWCwFN}.

  Lemma nnp_bij
    : cancel (nnp_l (C:= C)) (ctl_c (C:= C))
    /\ cancel (ctl_c (C:= C)) (nnp_l (C:= C)).
  Proof.

    exact (conj nnp_cl nnp_lc).
  Qed.

  Lemma nnp_l_bijective : bijective (@nnp_l C _).
  Proof.
    apply (@Bijective _ _ _ ctl_c); apply nnp_bij.
  Qed.
  Lemma nnp_l_injective : ssrfun.injective (@nnp_l C _).
  Proof.
    apply (bij_inj (nnp_l_bijective)).
  Qed.

  Lemma ctl_c_bijective : bijective (@ctl_c C).
  Proof.
    apply (@Bijective _ _ _ nnp_l); apply nnp_bij.
  Qed.

  Lemma ctl_c_0 : ctl_c (0:nat) = ⋆_C.
  Proof.
    symmetry.
    assert (E := (@nnp_cl C _ (ctl_c 0))).
    rewrite (snd nnp_bij (0:nat)) in E.
    exact E.
  Qed.

  Lemma ctl_c_S (m:nat) : @eq C (ctl_c (S m)) (s (ctl_c m)).
  Proof. reflexivity. Qed.

  Lemma nnp_l_distobj : nnp_l (⋆_C) = (0:nat).
  Proof.
    symmetry.
    rewrite <- (snd nnp_bij (0:nat)).
    reflexivity.
  Qed.

  Lemma nnp_l_s (m : C) : (nnp_l (s m)) = (S (nnp_l m)).
  Proof.
    symmetry.
    rewrite <- (snd nnp_bij (S (nnp_l m))).
    f_equal.
    simpl.
    f_equal.
    apply nnp_bij.
  Qed.

Section UWCwFN_induction.

  Definition UWCwFN_ind' (P : ctx C -> Type)
    (f0 : P (ctl_c 0))
    (fS : forall m:nat, P (ctl_c m) -> P(ctl_c (S m)))
    :forall (m :nat), P (ctl_c m) .
  Proof.
    induction m.
    - exact f0.
    - exact (fS _ IHm).
  Defined.
  Lemma UWCwFN_ind'_beta_0 {P : ctx C -> Type}
    (f0 : P (ctl_c 0))
    (fS : forall m:nat, P (ctl_c m) -> P(ctl_c (S m)))
    : UWCwFN_ind' P f0 fS 0 = f0.
  Proof.
    reflexivity.
  Abort.
  Definition UWCwFN_ind (P : ctx C -> Type)
    (f0 : P (⋆_ ctx C))
    (fS : forall m:ctx C, P (m) -> P(s m))
    :forall (m :ctx C), P m .
  Proof.
    intro m.
    apply (Logic.transport _ (nnp_cl m)).
    apply UWCwFN_ind'; clear m.
    - exact f0.
    - intros m p.
      exact (fS _ p).
  Defined.

End UWCwFN_induction.

End UWCwFN_properties.


Arguments nnp_bij _ : clear implicits.
Arguments nnp_l_bijective _ : clear implicits.
Arguments ctl_c_bijective _ : clear implicits.
Arguments ctl_c_0 _ : clear implicits.
Arguments nnp_l_distobj _ : clear implicits.

Arguments UWCwFN_ind {_}.

Section nnp_PathAlgebra.
  Context (C:UWCwFN).

  Let ctl_c := @ctl_c C.

  Context {m : C} (n:nat)
  (aδ : Tm m * (m ~>  (ctl_c (nnp_l (ctl_c n))))).

  Context (f : forall n, @SetoidMorphism
    (Tm m * (m ~>  (ctl_c (nnp_l (ctl_c n))))) _
    (Tm m * (m ~>  s (ctl_c n))) _).

  Lemma nnp_higher_clc : f_equal ctl_c (nnp_lc n) = nnp_cl (ctl_c n).
  Proof.
    unfold nnp_cl.
    apply eq_trans_invl.
    symmetry.
    eapply eq_trans.
    { apply (f_equal (fun x => eq_trans x _)).
      apply (f_equal (fun x => f_equal ctl_c x)).
      exact (homot_trivial _ nnp_lc). }
    eapply eq_trans.
    { apply (f_equal (fun x => eq_trans x _)).
      apply (f_equal_compose  (λ x : nat, nnp_l (ctl_c x)) ctl_c (nnp_lc n)). }
    exact (eq_sym (homot_naturality
      (λ x, ctl_c (nnp_l (ctl_c x)))
      ctl_c
      (λ x, (nnp_cl' (ctl_c x)) )
      (nnp_lc n))).
  Qed.

End nnp_PathAlgebra.
Arguments nnp_higher_clc {C} _.

Section UIP_ctx.

  Context {C:UWCwFN}.

  Lemma ctx_dec (x y : C) : {x = y} + {x ≠ y}.
  Proof.
    rewrite <-(nnp_cl x), <-(nnp_cl y).
    destruct (Nat.eq_dec (nnp_l x) (nnp_l y)).
    - destruct e.
      left.
      reflexivity.
    - right.
      intro abs.
      specialize (f_equal nnp_l abs) as H.
      rewrite !nnp_cl in H.
      exact (n H).
  Qed.

  Lemma UIP_ctx (x y : C) (p1 p2 : x = y) : p1 = p2.
  Proof.
    apply Eqdep_dec.UIP_dec.
    apply ctx_dec.
  Qed.

  Lemma UIP_refl_ctx {x : C} (p : x = x)
    : p = eq_refl.
  Proof.
    apply (EqdepFacts.UIP__UIP_refl _ UIP_ctx).
  Qed.
End UIP_ctx.

Open Scope nat.
Lemma nnp_l_iter {C: UWCwFN} {n: C} (i:nat)
  : nnp_l (iter i s n) = i + nnp_l n.
Proof.
  induction i.
  - reflexivity.
  - change (iter (S i) s n) with (s (iter i s n)).
    rewrite (nnp_l_s (iter i s n)).
    now rewrite IHi.
Qed.

Lemma ctl_c_add {C: UWCwFN} (i n:nat)
  : ctl_c (i + n) = iter i (@s C) (ctl_c n).
Proof.
  induction i.
  - reflexivity.
  - change (iter (S i) s (ctl_c n)) with (@s C (iter i s (ctl_c n))).
    refine (eq_trans _ _).
    + reflexivity.
    + simpl.
      f_equal.
      exact IHi.
Defined.
Close Scope nat.


Section NNP_lemmas.
  Context {C : UWCwFN}.

  Definition max_ctx (n m : C) : C
    := ctl_c (max (nnp_l n) (nnp_l m)).

  Lemma max_ctx_distobj (m:C) : max_ctx (⋆_C) m = m.
  Proof.
    unfold max_ctx.
    rewrite nnp_l_distobj; simpl; rewrite nnp_cl.
    reflexivity.
  Qed.

  Lemma max_ctx_s_distobj (n:C) : max_ctx (s n) (⋆_C) = s n.
  Proof.
    unfold max_ctx.
    rewrite nnp_l_s, nnp_l_distobj; simpl; rewrite nnp_cl.
    reflexivity.
  Qed.

  Lemma max_ctx_s_s (n m:C) : max_ctx (s n) (s m) = s (max_ctx n m).
  Proof.
    unfold max_ctx.
    rewrite !nnp_l_s.
    reflexivity.
  Qed.

  Lemma nnp_l_max (n m : C) : nnp_l (max_ctx n m) = max (nnp_l n) (nnp_l m).
  Proof.
    revert m.
    induction n using UWCwFN_ind; intros m0.
    - rewrite max_ctx_distobj, nnp_l_distobj.
      reflexivity.
    - induction m0 using UWCwFN_ind.
      + rewrite max_ctx_s_distobj, nnp_l_distobj, Nat.max_0_r.
        reflexivity.
      + rewrite max_ctx_s_s, !nnp_l_s, <-Nat.succ_max_distr.
        f_equal.
        apply IHn.
  Qed.

  Definition max_ctx_diff_l (n m : C)
    := ((max (nnp_l n) (nnp_l m)) - (nnp_l n))%nat.
  Definition max_ctx_diff_r (n m : C)
    := ((max (nnp_l n) (nnp_l m)) - (nnp_l m))%nat.

  Lemma max_ctx_to_iter_l (n m : C)
    : max_ctx n m = iter (max_ctx_diff_l n m) s n.
  Proof.
    apply nnp_l_injective.
    rewrite nnp_l_max, nnp_l_iter.
    unfold max_ctx_diff_l.
    lia.
  Qed.
  Lemma max_ctx_to_iter_r (n m : C)
    : max_ctx n m = iter (max_ctx_diff_r n m) s m.
  Proof.
    apply nnp_l_injective.
    rewrite nnp_l_max, nnp_l_iter.
    unfold max_ctx_diff_r.
    lia.
  Qed.

  Lemma iter_nnp_l_surjective {m n : C} (le : (nnp_l m <= nnp_l n)%nat)
  : n = iter (nnp_l n - nnp_l m) s m.
  Proof.
    apply nnp_l_injective.
    rewrite !nnp_l_iter.
    lia.
  Qed.

End NNP_lemmas.