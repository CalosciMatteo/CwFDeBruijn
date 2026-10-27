From CwFdeBruijn.Syntax.AKcf Require Export AKcf.
From Stdlib Require Import Structures.Equalities Bool.

(* Algorithms to know if δ and x are such thatù
 [Tmscf_snoc δ x] can be eta reduced (at the top) *)

Inductive etaRelatedP : Tmscf -> Tmcf -> Prop :=
  EtaRelatedP (δ:Tmscf) : etaRelatedP (Tmscf_π₁ δ) (Tmcf_π₂ δ).

Definition etaRelatedb (δ : Tmscf) (x : Tmcf) : bool :=
match δ with
  | Tmscf_π₁ δ =>
  match x with
    | Tmcf_π₂ δ' => Tmscf_beq δ δ'
    | _ => false
  end
  | _ => false
end.

Lemma etaRelated_spec (δ : Tmscf) (x : Tmcf)
  : reflect (etaRelatedP δ x) (etaRelatedb δ x).
Proof.
  apply iff_reflect.
  split.
  - intro H. induction H. cbn.
    apply (introT (Tmscf_eq_spec _ _)).
    reflexivity.
  - destruct δ, x; simpl; intro H; try (exfalso; apply (diff_false_true H)).
    induction (elimT (Tmscf_eq_spec _ _) H).  
    constructor.
Qed.

Lemma etaRelatedP_tosig {δ x} (Hη : etaRelatedP δ x)
  : {δ' | δ = Tmscf_π₁ δ' /\ x = Tmcf_π₂ δ'}.
Proof.
  destruct δ, x;
  try (exfalso; apply (diff_false_true (introT (etaRelated_spec _ _) Hη))).
  split with δ; split.
  - reflexivity.
  - f_equal; symmetry.
    apply (elimT (Tmscf_eq_spec _ _)).
    apply (introT (etaRelated_spec _ _) Hη).
Qed.

Lemma etaRelatedP_Tmcf_eq {δ x} : etaRelatedP (Tmscf_π₁ δ) x -> x = Tmcf_π₂ δ.
Proof.
  induction x;
  intro H; inversion H.
  reflexivity.
Qed.