From CwFdeBruijn.Syntax.Sigma Require Import Sigma.
From CwFdeBruijn.Syntax.SUBST.OG Require Import OGSUBST.


Open Scope AS_scope.
Open Scope OGSUBST_scope.

Fixpoint SUBST_of_TmAS (x:TmAS) {struct x} : OGSUBST := match x with
| a [δ] => (SUBST_of_TmAS a) ○ (SUBST_of_TmsAS δ)
| 0 => S
| a @ b => < (SUBST_of_TmAS a) , (SUBST_of_TmAS b) >
| λ a => Λ (SUBST_of_TmAS a)
end
with SUBST_of_TmsAS (δ : TmsAS) {struct δ} : OGSUBST := match δ with
| <δ,a>%AS => < (SUBST_of_TmsAS δ) , (SUBST_of_TmAS a) >
| id => I
| S%AS => F
| (δ ○ γ)%AS => (SUBST_of_TmsAS δ) ○ (SUBST_of_TmsAS γ)
end.

Fixpoint TmASσstep_to_SUBSTR {a a':TmAS} (H : (a --> a')%AS) : (SUBST_of_TmAS a) --> (SUBST_of_TmAS a')
with TmsASσstep_to_SUBSTR {δ δ' :TmsAS} (H: δ --s> δ') : (SUBST_of_TmsAS δ) --> (SUBST_of_TmsAS δ').
Proof.
{ induction H.
  { induction H. 
    - apply OGSUBSTR_IdR.  
    - apply OGSUBSTR_Snd.    
    - apply OGSUBSTR_DPair.
    - apply OGSUBSTR_DΛ.
    - apply OGSUBSTR_Ass.
     }
  all: cbn.
  - apply OGSUBSTR_Comp_L; assumption.
  - apply OGSUBSTR_Comp_R. apply (TmsASσstep_to_SUBSTR _ _ H).
  - apply OGSUBSTR_Pairing_L; assumption.
  - apply OGSUBSTR_Pairing_R; assumption.
  - apply OGSUBSTR_Λ; assumption. }
{ induction H.
  { induction H.
    - apply OGSUBSTR_IdL.
    - apply OGSUBSTR_IdR.
    - apply OGSUBSTR_Fst.
    - apply OGSUBSTR_DPair.
    - apply OGSUBSTR_Ass.
    - apply OGSUBSTR_FSI.
    - apply OGSUBSTR_SPair. }
  all: cbn.
  - apply OGSUBSTR_Pairing_L. assumption.
  - apply OGSUBSTR_Pairing_R. apply (TmASσstep_to_SUBSTR _ _ H).
  - apply OGSUBSTR_Comp_L; assumption.
  - apply OGSUBSTR_Comp_R; assumption. }
Qed.

Close Scope OGSUBST_scope.