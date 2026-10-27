From Stdlib Require Export Psatz.
From Stdlib Require Export Program.
From Stdlib Require Export Relations.
Require Export Ltac.
Require Export ssrbool.
From CwFdeBruijn Require Export Setup.ListOps Setup.GenRewr.
Require Import Setoid RelationClasses Morphisms.

Axiom extensionality :
    forall {X Y} (f g : X -> Y) (H : forall x : X, f x = g x), f = g.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert := solve_by_inverts 1.

Fixpoint iter {X} (f: X -> X) (i:nat) : X -> X:=
  match i with
  | 0 => fun x => x
  | S i' => fun x => f (iter f i' x)
  end.

Lemma iter_flip {X} (f:X->X) i x : iter f (S i) x = (iter f i (f x)).
Proof.
  revert x.
  induction i; intro x.
  + reflexivity.
  + simpl.
    f_equal.
    apply IHi.
Qed.

Notation pred := Nat.pred.

(* Normal Forms *)
Definition normal_form {X:Type} (R:relation X) (x:X) : Prop := ~ exists x', R x x'.

Definition normalize {X:Type} (R:relation X) (x:X) := { y | (clos_refl_trans _ R) x y /\ normal_form R y}.

Definition nffun {X:Type} {R:relation X} {x:X} (H: normalize R x) : X
  := proj1_sig H.

Definition nffun_conv {X:Type} {R:relation X} {x:X} (H: normalize R x) : (clos_refl_trans _ R) x (nffun H)
  := proj1 (proj2_sig H).

Definition nffun_isnf {X:Type} {R:relation X} {x:X} (H: normalize R x) : normal_form R (nffun H)
  := proj2 (proj2_sig H).

Lemma normalize_refl {X:Type} (R:relation X) (x:X) (xN : normal_form R x) : normalize R x.
Proof.
  split with x.
  auto with sets.
Qed.

Lemma normalize_trans {X:Type} (R:relation X) (x y:X) (H : clos_refl_trans _ R x y) (yN : normalize R y) : normalize R x.
Proof.
  destruct yN as [z Hz].
  - split with z; split.
    + apply (rt_trans _ _ _ _ _ H).
      apply Hz.
    + apply Hz.
Qed.

Lemma normal_form_rt {X:Type} {R:relation X} {x y:X}
  (x_nf : normal_form R x)
  (red : clos_refl_trans _ R x y)
  : x = y.
Proof.
  destruct (clos_rt_rt1n _ _ _ _ red).
  - reflexivity.
  - exfalso.
    apply x_nf.
    eexists.
    apply H.
Qed.

Definition normal_form_uniqueness {X:Type} (R:relation X) := 
  forall  (x y y':X),
    (normal_form R y) -> (normal_form R y') ->
    (clos_refl_trans X R x y) -> (clos_refl_trans X R x y') ->
    y = y'.
    
Lemma nfuniqueness_iff_conv {X R} (uniq : normal_form_uniqueness R) (H : forall x, normalize R x) (x y : X)
: nffun (H x) = nffun (H y) <-> clos_refl_sym_trans X R x y.
Proof.
  split.
  - intros.
    eapply rst_trans with (nffun (H x)).
    { apply clos_rt_clos_rst.
      apply nffun_conv. }
    destruct (eq_sym H0).
    apply rst_sym.
    apply clos_rt_clos_rst.
    apply nffun_conv.
  - intro Z.
    apply clos_rst_rstn1_iff in Z.
    induction Z. { reflexivity. }
    destruct (eq_sym IHZ).
    destruct H0.
    + refine (uniq y _ _ _ _ _ _).
      * apply nffun_isnf.
      * apply nffun_isnf.
      * apply nffun_conv.
      * eapply rt_trans with z.
        { apply rt_step. apply H0. }
        apply nffun_conv.
    + refine (uniq z _ _ _ _ _ _).
      * apply nffun_isnf.
      * apply nffun_isnf.
      * eapply rt_trans with y.
        { apply rt_step. apply H0. }
        apply nffun_conv.
      * apply nffun_conv.
Qed.

Lemma nffun_nf {A R} {x:A} (H: normal_form R x)
  (normalizingH : forall x, normalize R x )
  : nffun (normalizingH x) = x.
Proof.
  destruct (normalizingH x) as [xnf [xredxnfis]].
  cbn.
  symmetry.
  eapply normal_form_rt.
  - exact H.
  - exact xredxnfis.
Qed.

(* Confluence *)
Definition confluencing {X:Type} (R:relation X) (y z : X) : Prop
  := exists x0, (clos_refl_trans X R y x0) /\ (clos_refl_trans X R z x0).

Definition confluenceAt {X:Type} (R R':relation X) (x:X) : Prop := forall (y z:X) (Hy : R x y) (Hz: R x z), confluencing R' y z.

Lemma confluencing_refl {X:Type} {R:relation X} (x:X)
  : confluencing R x x.
Proof.
  unfold confluencing.
  esplit; split; apply rt_refl.
Qed.

Lemma confluencing_comm {X:Type} {R:relation X} (x y:X)
  : confluencing R x y -> confluencing R y x.
Proof.
  intro H; destruct H as [x0 [redx redy]].
  esplit; split; eassumption.
Qed.

Lemma confluencing_red {X:Type} {R:relation X} (x y:X)
  : (clos_refl_trans X R x y) -> confluencing R x y.
Proof.
  intro H; split with y; auto with sets.
Qed.

Global Instance confluencing_reflexive {X:Type} {R:relation X} : Reflexive (confluencing R).
Proof.
  intros ? . 
  apply confluencing_refl.
Qed.

Global Instance confluencing_symmetric {X:Type} {R:relation X} : Symmetric (confluencing R).
Proof.
  intros ? . 
  apply confluencing_comm.
Qed.

Global Instance confluencing_proper {X:Type} {R:relation X} : Proper ((clos_refl_trans X R) ==> (clos_refl_trans X R) ==> (flip impl)) (confluencing R).
Proof.
  intros ? ? ? ? ? ? ?.
  destruct H1 as [join pjoin].
  split with join; split.
  - eapply rt_trans.
    + exact H.
    + apply pjoin.
  - eapply rt_trans.
    + exact H0.
    + apply pjoin.
Qed.

