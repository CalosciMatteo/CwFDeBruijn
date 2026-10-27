From CwFdeBruijn.Syntax.AKcf Require Export AKcf.
From Stdlib Require Import Bool.

Inductive Tmcfσisref0 : Tmcf -> Prop :=
  | Tmcfσisref0_ref0 : Tmcfσisref0 (Tmcf_π₂ Tmscf_id).

Definition Tmcfσisref0b (x:Tmcf) : bool :=
match x with
  | Tmcf_π₂ (Tmscf_id) => true
  | _ => false
end.

Lemma Tmcfσisref0_spec (x:Tmcf) : reflect (Tmcfσisref0 x) (Tmcfσisref0b x).
Proof.
  destruct x.
  2:{
    destruct δ.
    2:{
      apply ReflectT.
      apply Tmcfσisref0_ref0.
    }
    all :
      apply ReflectF;
      intro H;
      inversion H.
  }
  all :
    apply ReflectF;
    intro H;
    inversion H.
Qed.

Inductive TmcfσisrefP : Tmcf -> Prop :=
  | Tmcfσisref_ref (δ:Tmscf) (Hδ : cf_iter_π₁idP δ) : TmcfσisrefP (Tmcf_π₂ δ).

Definition Tmcfσisrefb (x:Tmcf) : bool :=
match x with
  | Tmcf_π₂ δ => cf_iter_π₁idb δ
  | _ => false
end.

Lemma Tmcfσisref_spec (x:Tmcf) : reflect (TmcfσisrefP x) (Tmcfσisrefb x).
Proof.
  destruct x.
  2:{
    destruct δ.
    2:{
      apply ReflectT.
      apply Tmcfσisref_ref.
      apply cf_iter_π₁idP_id.
    }
    3 : {
      simpl.
      apply (equivP (P:=(cf_iter_π₁idP δ))).
      - apply cf_iter_π₁id_spec.
      - split.
        + intro H.
          apply Tmcfσisref_ref.
          apply cf_iter_π₁idP_π₁.
          exact H.
        + intro H.
          inversion H.
          inversion Hδ.
          assumption.
    }
    all :
      apply ReflectF;
      intro H;
      inversion H;
      solve_by_invert.
  }
  all :
    apply ReflectF;
    intro H;
    inversion H.
Qed.

Definition TmcfσisrefP_rec
  (P : Tmcf -> Type)
  (X1 : forall δ : Tmscf, cf_iter_π₁idP δ -> P (Tmcf_π₂ δ))
  (t : Tmcf) (H : TmcfσisrefP t)
  : P t.
Proof.
  assert (E := (proj1 (reflect_iff _ _ (Tmcfσisref_spec t)) H)).
  induction t; try discriminate E.
  apply X1.
  destruct δ; try discriminate E.
  - constructor.
  - inversion H.
    exact Hδ.
Qed.

Lemma TmcfσisrefP_tosig {x} (Hx : TmcfσisrefP x)
  : { i & x = Tmcf_ref i}.
Proof.
  induction Hx.
  destruct (cf_iter_π₁idP_to_cf_iter_π₁id (δ:=δ)) as [i ?]; subst.
  - assumption.
  - split with i.
    reflexivity.
Qed.