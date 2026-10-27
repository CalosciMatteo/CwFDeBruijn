Require Import Setoid Morphisms RelationClasses.

From Stdlib Require Export Relations.

Definition rt_subrelation {A : Type} (RA : relation A) 
  : subrelation RA (clos_refl_trans A RA).
Proof.
  intros ? ? H.
  apply rt_step.
  exact H.
Qed.

Definition rst_subrelation {A : Type} (RA : relation A) 
  : subrelation RA (clos_refl_sym_trans A RA).
Proof.
  intros ? ? H.
  apply rst_step.
  exact H.
Qed.


Section clos_Instances.
  Context {A : Type} (RA : relation A).
  Global Instance TmASσconv_preorder : PreOrder (clos_refl_trans A RA).
  Proof.
    constructor.
    - intro; apply rt_refl.
    - intro; apply rt_trans.
  Qed.

  Global Instance TmASσeq_equivalence : Equivalence (clos_refl_sym_trans A RA).
  Proof.
    constructor; intro.
    - apply rst_refl.
    - apply rst_sym.
    - apply rst_trans.
  Qed.
End clos_Instances.

Section clos_refl_trans_Lifting'.
  Context {A B C : Type}.

  Definition rt_lift_proper_1' {RA : relation A} {RB : relation B}
    {RB_refl : Reflexive RB }
    {RB_trans : Transitive RB }
    (f : A -> B) 
    (H1 : Proper (RA ==> RB) f) : 
    Proper (clos_refl_trans A RA ==> RB) f.
  Proof.
    intros x y H_steps. induction H_steps.
    - apply H1. assumption.
    - reflexivity.
    - etransitivity; eassumption.
  Qed.
  Definition rst_lift_proper_1' {RA : relation A} {RB : relation B}
    {RB_refl : Reflexive RB }
    {RB_trans : Transitive RB }
    {RB_sym : Symmetric RB }
    (f : A -> B) 
    (H1 : Proper (RA ==> RB) f) : 
    Proper (clos_refl_sym_trans A RA ==> RB) f.
  Proof.
    intros x y H_steps. induction H_steps.
    - apply H1. assumption.
    - reflexivity.
    - now symmetry.
    - etransitivity; eassumption.
  Qed.
End clos_refl_trans_Lifting'.
Section clos_refl_trans_Lifting.
  Context {A B C : Type}
    (RA : relation A)
    (RB : relation B)
    (RC : relation C).
  
  Let RArt := clos_refl_trans A RA.
  Let RBrt := clos_refl_trans B RB.
  Let RCrt := clos_refl_trans C RC.

  (* Generic lifter for 1-argument functions *)
  Definition rt_lift_proper_1 (f : A -> B) 
    (H1 : Proper (RA ==> RBrt) f) : 
    Proper (RArt ==> RBrt) f.
  Proof.
    intros x y H_steps. induction H_steps.
    - apply H1. assumption.
    - reflexivity.
    - etransitivity; eassumption.
  Qed.

  (* Generic lifter for 2-argument functions *)
  Definition rt_lift_proper_2 (f : A -> B -> C)
    (Hleft  : Proper (RA ==> eq ==> RCrt) f)
    (Hright : Proper (eq ==> RB ==> RCrt) f) :
    Proper (RArt ==> RBrt ==> RCrt) f.
  Proof.
    assert (Hleft_multi : Proper (RArt ==> eq ==> RCrt) f).
    { intros x1 x2 Hx y1 y2 Hy. subst y2. induction Hx.
      - apply Hleft; auto.
      - reflexivity.
      - etransitivity; eassumption. }
    assert (Hright_multi : Proper (eq ==> RBrt ==> RCrt) f).
    { intros x1 x2 Hx y1 y2 Hy. subst x2. induction Hy.
      - apply Hright; auto.
      - reflexivity.
      - etransitivity; eassumption. }
    intros x1 x2 Hx y1 y2 Hy.
    etransitivity.
    - apply Hleft_multi; eauto.
    - apply Hright_multi; eauto.
  Qed.

End clos_refl_trans_Lifting.

Section clos_refl_sym_trans_Lifting.
  Context {A B C : Type}
    (RA : relation A)
    (RB : relation B)
    (RC : relation C).
  
  Let RArst := clos_refl_sym_trans A RA.
  Let RBrst := clos_refl_sym_trans B RB.
  Let RCrst := clos_refl_sym_trans C RC.

  (* Generic lifter for 1-argument functions *)
  Definition rst_lift_proper_1 (f : A -> B) 
    (H1 : Proper (RA ==> RBrst) f) : 
    Proper (RArst ==> RBrst) f.
  Proof.
    intros x y H_steps. induction H_steps.
    - apply H1. assumption.
    - reflexivity.
    - symmetry; eassumption.
    - etransitivity; eassumption.
  Qed.

  (* Generic lifter for 2-argument functions *)
  Definition rst_lift_proper_2 (f : A -> B -> C)
    (Hleft  : Proper (RA ==> eq ==> RCrst) f)
    (Hright : Proper (eq ==> RB ==> RCrst) f) :
    Proper (RArst ==> RBrst ==> RCrst) f.
  Proof.
    assert (Hleft_multi : Proper (RArst ==> eq ==> RCrst) f).
    { intros x1 x2 Hx y1 y2 Hy. subst y2. induction Hx.
      - apply Hleft; auto.
      - reflexivity.
      - symmetry; eassumption.
      - etransitivity; eassumption. }
    assert (Hright_multi : Proper (eq ==> RBrst ==> RCrst) f).
    { intros x1 x2 Hx y1 y2 Hy. subst x2. induction Hy.
      - apply Hright; auto.
      - reflexivity.
      - symmetry; eassumption.
      - etransitivity; eassumption. }
    intros x1 x2 Hx y1 y2 Hy.
    etransitivity.
    - apply Hleft_multi; eauto.
    - apply Hright_multi; eauto.
  Qed.

End clos_refl_sym_trans_Lifting.
