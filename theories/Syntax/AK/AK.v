From CwFdeBruijn.Syntax.dB Require Export dB TmP.

(* Scoped Model for the Untyped lambda calculus binding signature *)
Inductive Tms : forall (p q : nat), Type :=
  | Tms_nil p : Tms p 0
  | Tms_snoc {p q : nat} (δ : Tms p q) (x : Tm p) : Tms p (S q)
  | Tms_id p : Tms p p
  | Tms_comp {q r} (δ₁ : Tms q r) {p} (δ₂ : Tms p q) : Tms p r
  | Tms_π₁ {p q} (δ : Tms p (S q)) : Tms p q
with Tm : forall p, Type :=
  | Tm_subst {q} (x : Tm q) {p} (δ : Tms p q) : Tm p
  | Tm_π₂ {p q} (δ : Tms p (S q)) : Tm p
  | Tm_app {p} (x y: Tm p) : Tm p
  | Tm_lam {p} (x : Tm (S p)) : Tm p.

Definition liftin {p q} (δ : Tms p q) : Tms (S p) (q) :=
  (Tms_comp δ (Tms_π₁ (Tms_id (S p)))).

Definition lift {p q} (δ : Tms p q) : Tms (S p) (S q) :=
  Tms_snoc (liftin δ) (Tm_π₂ (Tms_id (S p))).

Fixpoint iter_π₁ {p} i : forall {q}, Tms p (i + q) -> Tms p q :=
  match i return forall q, Tms p (i + q) -> Tms p q with
  | 0 => fun q δ => δ
  | S i' => fun q δ => iter_π₁ i' (Tms_π₁ δ)
  end.

Definition iter_π₂ {p q} i (δ : Tms p (i + S q)) :=
  Tm_π₂ (iter_π₁ i δ).

Definition Tm_ref i q : Tm (i + S q) :=
  iter_π₂ i (Tms_id (i + S q)).

Definition Tm_cast {p q} (Heq : p = q) (x : Tm p) : Tm q.
Proof.
  elim Heq.
  exact x.
Defined.