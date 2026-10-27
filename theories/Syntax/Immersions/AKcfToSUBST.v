From CwFdeBruijn.Syntax.AKcf Require Import AKcf AKcf_Conv.
From CwFdeBruijn.Syntax.SUBST Require Import SUBST.

Open Scope SUBST_scope.

Fixpoint SUBST_of_Tmcf (x:Tmcf) : SUBST := match x with
| Tmcf_subst a δ => (SUBST_of_Tmcf a) ○ (SUBST_of_Tmscf δ)
| Tmcf_π₂ δ => S ○ (SUBST_of_Tmscf δ)
| Tmcf_app a b => < (SUBST_of_Tmcf a) , (SUBST_of_Tmcf b) >
| Tmcf_lam a => Λ (SUBST_of_Tmcf a)
end
with SUBST_of_Tmscf (δ : Tmscf) {struct δ} : SUBST := match δ with
| Tmscf_snoc δ a => < (SUBST_of_Tmscf δ) , (SUBST_of_Tmcf a) >
| Tmscf_id => I
| Tmscf_comp δ γ => (SUBST_of_Tmscf δ) ○ (SUBST_of_Tmscf γ)
| Tmscf_π₁ δ => F ○ (SUBST_of_Tmscf δ)
end.

Fixpoint Tmcfσstep_to_SUBSTR {a a':Tmcf} (H : (a --> a')%AKcf) : (SUBST_of_Tmcf a) --> (SUBST_of_Tmcf a')
with Tmscfσstep_to_SUBSTR {δ δ' :Tmscf} (H: (δ --s> δ')%AKcf) : (SUBST_of_Tmscf δ) --> (SUBST_of_Tmscf δ').
Proof.
{ induction H.
  { induction H. 
    - cbn. apply SUBSTR_Ass.
    - apply SUBSTR_Snd.
    - apply SUBSTR_DΛ.
    - apply SUBSTR_Ass.
    - apply SUBSTR_DPair. }
  all: cbn.
  - apply SUBSTR_Comp_L; assumption.
  - apply SUBSTR_Comp_R. apply (Tmscfσstep_to_SUBSTR _ _ H).
  - apply SUBSTR_Comp_R. apply (Tmscfσstep_to_SUBSTR _ _ H).
  - apply SUBSTR_Pairing_L; assumption.
  - apply SUBSTR_Pairing_R; assumption.
  - apply SUBSTR_Λ; assumption. }
{ induction H.
  { induction H.
    - apply SUBSTR_IdL.
    - apply SUBSTR_IdR.
    - apply SUBSTR_Ass.
    - apply SUBSTR_DPair.
    - apply SUBSTR_Fst.
    - apply SUBSTR_Ass.
    - apply SUBSTR_SPair. }
  all: cbn.
  - apply SUBSTR_Pairing_L. assumption.
  - apply SUBSTR_Pairing_R. apply (Tmcfσstep_to_SUBSTR _ _ H).
  - apply SUBSTR_Comp_L; assumption.
  - apply SUBSTR_Comp_R; assumption.
  - apply SUBSTR_Comp_R; assumption. }
Qed.

Close Scope SUBST_scope.