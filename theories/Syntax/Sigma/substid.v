From CwFdeBruijn.Syntax.Sigma Require Import Sigma.

Open Scope AS_scope.

Lemma AS_lift_id : lift id --s>* id.
Proof.
  unfold lift.
  now rewrite AS_idl, AS_etaid.
Qed.

Fixpoint AS_subst_id {t:TmAS} : t[id] -->* t
with AS_idr {δ : TmsAS} : δ ○ id --s>* δ.
Proof.
{ induction t.
  - now rewrite AS_0id.
  - now rewrite AS_appsubst, IHt1, IHt2.
  - now rewrite AS_substsubst, AS_idr.
  - now rewrite AS_lamsubst, AS_lift_id, IHt.
}
{ induction δ.
  - now rewrite AS_idl.
  - now rewrite AS_Sid.
  - now rewrite AS_snocomp, IHδ, AS_subst_id.
  - now rewrite AS_ass, IHδ2.
}
Qed.