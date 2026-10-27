From Category Require Import Lib Theory.
From Category Require Import Lib.TList.
From Category Require Import Construction.Free.Quiver.

(* Free category genertaed by one endomorphism *)

(* Quiver with one node and one arrow *)
Definition OneEndo_Quiver : Quiver := {|
  nodes := poly_unit;
  edges := (λ t t', poly_unit );
  edgeset := (λ t t', unit_setoid)
|}.

Definition OneEndo_Category := FreeOnQuiver OneEndo_Quiver.


Definition OneEndo_arrow : ttt ~{OneEndo_Category}~> ttt.  
Proof.
  refine (TList.tcons ttt ttt (TList.tnil)).
Defined.

Lemma OneEndo_arrow_S
  (f : ttt ~{ OneEndo_Category }~> ttt)
  : TList.tcons ttt ttt f ≈[OneEndo_Category] f ∘[OneEndo_Category] OneEndo_arrow.
Proof.
  rewrite tlist_app_cons.
  reflexivity.
Qed.