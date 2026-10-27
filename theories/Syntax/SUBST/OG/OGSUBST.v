(*
Implementation of the SUBST rewriting system as presented in

[T. Hardin and À. Laville, Proof of Termination of The Rewriting System Subst on C.C.L. Theoretical Computer Sc., 46, pp 305-312, 1986.]

[https://inria.hal.science/inria-00075994/file/RR-0560.pdf]

*)


From CwFdeBruijn.Syntax.Setup Require Export RelationsLemmas.

Inductive OGSUBST : Type :=
| OGSUBST_F : OGSUBST
| OGSUBST_S : OGSUBST
| OGSUBST_I : OGSUBST
| OGSUBST_Λ : OGSUBST -> OGSUBST
| OGSUBST_Pairing : OGSUBST -> OGSUBST -> OGSUBST
| OGSUBST_Comp : OGSUBST -> OGSUBST -> OGSUBST.

Declare Scope OGSUBST_scope.
Delimit Scope OGSUBST_scope with OGSBS.


Open Scope OGSUBST_scope.

Notation "'F'" := (OGSUBST_F) (at level 5) : OGSUBST_scope.
Notation "'S'" := (OGSUBST_S) (at level 5) : OGSUBST_scope.
Notation "'I'" := (OGSUBST_I) (at level 5) : OGSUBST_scope.
Notation "'Λ'" := (OGSUBST_Λ) (at level 5) : OGSUBST_scope.
Notation "'<' s ',' t '>'" := (OGSUBST_Pairing s t) (s at level 40, t at level 40) : OGSUBST_scope.
Notation "s '○' t" := (OGSUBST_Comp s t) (at level 9) : OGSUBST_scope.

(* Rewrite rules *)
Inductive OGSUBSTR_step : relation OGSUBST :=
  | OGSUBSTR_Ass {s t u} : OGSUBSTR_step ((s○t)○ u) (s○(t○u))
  | OGSUBSTR_IdL {t} : OGSUBSTR_step (I○t) t
  | OGSUBSTR_IdR {t} : OGSUBSTR_step (t○I) t
  | OGSUBSTR_Fst {s t} : OGSUBSTR_step (F ○ <s,t>) s
  | OGSUBSTR_Snd {s t} : OGSUBSTR_step (S ○ <s,t>) t
  | OGSUBSTR_DPair {s t u} : OGSUBSTR_step (<s,t>○u) <s○u,t○u>
  | OGSUBSTR_SPair {t} : OGSUBSTR_step <F○t,S○t> t
  | OGSUBSTR_FSI : OGSUBSTR_step (< F , S >) I
  | OGSUBSTR_DΛ {s t} : OGSUBSTR_step ((Λ s) ○ t) (Λ (s○<t○F,S>)) 
  (* Congruence rules *)
  | OGSUBSTR_Λ {t' t} : OGSUBSTR_step t' t -> OGSUBSTR_step (Λ t') ( Λ t )
  | OGSUBSTR_Pairing_L {s' s t} : OGSUBSTR_step s' s -> OGSUBSTR_step < s' , t > < s , t >
  | OGSUBSTR_Pairing_R {s t' t} : OGSUBSTR_step t' t -> OGSUBSTR_step < s , t' > < s , t >
  | OGSUBSTR_Comp_L {s' s t} : OGSUBSTR_step s' s -> OGSUBSTR_step (s' ○  t) ( s ○ t )
  | OGSUBSTR_Comp_R {s t' t} : OGSUBSTR_step t' t -> OGSUBSTR_step (s  ○ t') ( s ○ t ).
Notation " s '-->' t " := (OGSUBSTR_step s t) (at level 55, t at level 55) : OGSUBST_scope.
Definition OGSUBSTR_conv := clos_refl_trans OGSUBST OGSUBSTR_step.
Notation " s '-->*' t " := (OGSUBSTR_conv s t) (at level 55, t at level 55) : OGSUBST_scope.

Close Scope OGSUBST_scope.