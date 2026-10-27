(*
Implementation of the SUBST rewriting system as presented in

[T. Hardin and À. Laville, Proof of Termination of The Rewriting System Subst on C.C.L. Theoretical Computer Sc., 46, pp 305-312, 1986.]

[https://inria.hal.science/inria-00075994/file/RR-0560.pdf]

We just change the rule DΛ, by adding [○I], we wonder if a termination proof can be adapted

*)

From Stdlib Require Export CMorphisms.
From CwFdeBruijn.Syntax.Setup Require Export RelationsLemmas.

Inductive SUBST : Type :=
| SUBST_F : SUBST
| SUBST_S : SUBST
| SUBST_I : SUBST
| SUBST_Λ : SUBST -> SUBST
| SUBST_Pairing : SUBST -> SUBST -> SUBST
| SUBST_Comp : SUBST -> SUBST -> SUBST.

Declare Scope SUBST_scope.
Delimit Scope SUBST_scope with SBS.

Notation "'F'" := (SUBST_F) (at level 5) : SUBST_scope.
Notation "'S'" := (SUBST_S) (at level 5) : SUBST_scope.
Notation "'I'" := (SUBST_I) (at level 5) : SUBST_scope.
Notation "'Λ'" := (SUBST_Λ) (at level 5) : SUBST_scope.
Notation "'<' s ',' t '>'" := (SUBST_Pairing s t) (s at level 40, t at level 40) : SUBST_scope.
Notation "s '○' t" := (SUBST_Comp s t) (at level 40) : SUBST_scope.

Open Scope SUBST_scope.

(* Rewrite rules *)
Inductive SUBSTR_step : relation SUBST :=
  | SUBSTR_Ass {s t u} : SUBSTR_step ((s○t)○ u) (s○(t○u))
  | SUBSTR_IdL {t} : SUBSTR_step (I○t) t
  | SUBSTR_IdR {t} : SUBSTR_step (t○I) t
  | SUBSTR_Fst {s t} : SUBSTR_step (F ○ <s,t>) s
  | SUBSTR_Snd {s t} : SUBSTR_step (S ○ <s,t>) t
  | SUBSTR_DPair {s t u} : SUBSTR_step (<s,t>○u) <s○u,t○u>
  | SUBSTR_SPair {t} : SUBSTR_step <F○t,S○t> t
  | SUBSTR_FSI : SUBSTR_step (< F , S >) I
  | SUBSTR_DΛ {s t} : SUBSTR_step ((Λ s) ○ t) (Λ (s○<t○(F○I),(S○I)>)) 
  (* Congruence rules *)
  | SUBSTR_Λ {t' t} : SUBSTR_step t' t -> SUBSTR_step (Λ t') ( Λ t )
  | SUBSTR_Pairing_L {s' s t} : SUBSTR_step s' s -> SUBSTR_step < s' , t > < s , t >
  | SUBSTR_Pairing_R {s t' t} : SUBSTR_step t' t -> SUBSTR_step < s , t' > < s , t >
  | SUBSTR_Comp_L {s' s t} : SUBSTR_step s' s -> SUBSTR_step (s' ○  t) ( s ○ t )
  | SUBSTR_Comp_R {s t' t} : SUBSTR_step t' t -> SUBSTR_step (s  ○ t') ( s ○ t ).
Notation " s '-->' t " := (SUBSTR_step s t) (at level 55, t at level 55) : SUBST_scope.
Definition SUBSTR_conv := clos_refl_trans SUBST SUBSTR_step.
Notation " s '-->*' t " := (SUBSTR_conv s t) (at level 55, t at level 55) : SUBST_scope.

#[export] Instance App_proper : Proper (SUBSTR_step ==> SUBSTR_step ==> SUBSTR_conv) SUBST_Comp.
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  eapply rt_trans; eapply rt_step.
  - apply (SUBSTR_Comp_L Hx).
  - apply (SUBSTR_Comp_R Hy).
Qed.
#[export] Instance SUBSTR_Comp_proper : Proper (SUBSTR_step ==> SUBSTR_step ==> SUBSTR_conv) SUBST_Comp.
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  eapply rt_trans; eapply rt_step.
  - apply (SUBSTR_Comp_L Hx).
  - apply (SUBSTR_Comp_R Hy).
Qed.
#[export] Instance SUBSTR_Pairing_proper : Proper (SUBSTR_step ==> SUBSTR_step ==> SUBSTR_conv) SUBST_Pairing.
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  eapply rt_trans; eapply rt_step.
  - apply (SUBSTR_Pairing_L Hx).
  - apply (SUBSTR_Pairing_R Hy).
Qed.

Close Scope SUBST_scope.