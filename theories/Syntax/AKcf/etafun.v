From CwFdeBruijn.Syntax.AKcf Require Export occur_Lemmas context AKcf_Conv Conv_Lemmas context_Lemmas.
From Stdlib Require Import Bool.

(* Here we repeatedly apply eta transformations in order to
  convert the output of Tmscf_of_Assign' in normal form *)

Definition ηfun (δ : Tmscf) : Tmscf :=
match δ with
| Tmscf_snoc σ x => if etaRelatedb σ x then
                      match σ with 
                      | Tmscf_π₁ τ => τ
                      | _ => δ
                      end
                      else δ
| _ => δ
end.

Fixpoint recηfun (δ : Tmscf) : Tmscf :=
match δ with
| Tmscf_snoc σ x => ηfun (Tmscf_snoc (recηfun σ) x)
| _ => δ 
end.

(* We are interested in applying [recηfun] only to substituitions
built from ref, π₁ and id (that are the one named Renaming) *)

Lemma recηfun_nf (δ : Tmscf) (UDC : Renaming δ)
: Tmscfσvalue (recηfun δ).
Proof.
  induction UDC.
  - induction Hδ.
    all: repeat constructor.
    assumption.
  - cbn -[etaRelatedb].
    destruct (reflect_dec _ _ (etaRelated_spec (recηfun δ) x)).
    + rewrite (introT (etaRelated_spec _ _) e).
      destruct e.
      apply Tmscfσvalue_iterπ₁id.
      inversion Hx.
      assumption.
    + rewrite (introF (etaRelated_spec _ _) n).
      apply Tmscfσvalue_snoc; try assumption.
      apply (Tmcfσvalue_ref' Hx).
Qed.

Lemma ηfun_σconv (δ : Tmscf) : δ --s>* ηfun δ.
Proof.
  destruct δ; simpl; autored.
  destruct (reflect_dec _ _ (etaRelated_spec δ x)).
  - rewrite (introT (etaRelated_spec _ _) e).
    destruct e.
    autored. 
  - rewrite (introF (etaRelated_spec _ _) n).
    autored.
Qed.

Lemma recηfun_σconv (δ : Tmscf) : δ --s>* recηfun δ.
Proof.
  induction δ.
  all: try autored.
  cbn.
  destruct (reflect_dec _ _ (etaRelated_spec (recηfun δ) x)).
  - rewrite (introT (etaRelated_spec _ _) e).
    destruct (recηfun δ).
    all: autored.
    eapply rt_trans.
    { eapply HINTsnoc_Tmscf_step_compatibility.
      exact IHδ. }
    rewrite (etaRelatedP_Tmcf_eq e).
    autored.
  - rewrite (introF (etaRelated_spec _ _) n).
    autored.
Qed.

Lemma recηfun_cf_iter_π₁ {n} : recηfun (cf_iter_π₁ n Tmscf_id) = cf_iter_π₁ n Tmscf_id.
Proof.
  destruct n; reflexivity.
Qed.

Lemma ηfun_cfassign {p q δ} (ass : cfassign p q δ) : cfassign p q (ηfun δ).
Proof.
  induction δ; cbn; try assumption.
  destruct (reflect_dec _ _ (etaRelated_spec δ x)).
  - rewrite (introT (etaRelated_spec _ _) e).
    destruct δ; inversion e; subst.
    inversion ass; subst.
    inversion Hδ; subst.
    assumption.
  - rewrite (introF (etaRelated_spec _ _) n).
    assumption.
Qed.