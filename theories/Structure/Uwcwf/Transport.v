From Stdlib Require Import Nat PeanoNat.
From Category Require Import Theory Lib Instance.Sets.
From CwFdeBruijn Require Import Lib.Transport CatPsh Uwcwf Structure.Uwcwf.
From CwFdeBruijn Require Import Contextual.

Lemma pi1_transport {C: UWCwF} {m n n' :C} (δ : m ~> s n) (p : n = n')
  : π1 (Logic.transport (λ x , m ~> x) (f_equal s p) δ)
    = Logic.transport (λ x , m ~> x) p (π1 δ).
Proof.
  destruct p.
  reflexivity.
Qed.

Lemma pi2_transport {C: UWCwF} {m n n' :C} (δ : m ~> s n) (p : n = n')
  : π2 (Logic.transport _(f_equal s p) δ)
    = Logic.transport _ p (π2 δ).
Proof.
  destruct p.
  reflexivity.
Qed.
Lemma pi2_transport_m {C: UWCwF} {m' m n :C} (δ : m' ~> s n) (p : m' = m)
  : π2 (Logic.transport (λ x, x ~{C}~> s n) p δ)
    = Logic.transport (λ x, fobj[Tm] x) p (π2 δ).
Proof.
  destruct p.
  reflexivity.
Qed.

Lemma homcast_π1 {C : UWCwF} {m m' n n' : C}
  (p_m: m = m')
  (p_n: n = n')
  (δ : m ~> s n)
  : homcast p_m p_n (π1 δ) = π1 (homcast p_m (f_equal s p_n) δ).
Proof.
  destruct p_m, p_n.
  reflexivity.
Qed.

Lemma pi2_homcast_2path {C : UWCwF} {m m' n n1 n2 : C}
  (p_m1: m = m')
  (p_m2: m = m')
  (p_n1: n = s n1)
  (p_n2: n = s n2)
  
  (En : n1 = n2)
  (E2n : Logic.transport (λ x, n = s x) En p_n1 = p_n2)
  (E2m : p_m1 = p_m2)

  
  (δ : m ~> n)
  : π2 (homcast p_m1 p_n1 δ) = π2 (homcast p_m2 p_n2 δ).
Proof.
  destruct p_m1, En.

  simpl in *.
  rewrite E2n, <-E2m.
  reflexivity.
Qed.

Lemma homcast_π2 {C : UWCwF} {m m' n n' : C}
  (p_m: m = m')
  (p_n: n = n')
  (δ : m ~> s n)
  : Logic.transport (λ x, fobj[Tm] x) p_m (π2 δ) = π2 (homcast p_m (f_equal s p_n) δ).
Proof.
  destruct p_m, p_n.
  reflexivity.
Qed.

Lemma homcast_π2' {C : UWCwF} {m m' n n' : C}
  (p_m: m = m')
  (p_n: n = n')
  (p_sn:s n = s n')
  (E : p_sn = f_equal s p_n )
  (δ : m ~> s n)
  : Logic.transport (λ x, fobj[Tm] x) p_m (π2 δ) = π2 (homcast p_m p_sn δ).
Proof.
  destruct p_m, p_n.
  rewrite E.
  reflexivity.
Qed.

(* Since NNP contexts are an hset,
  we can generalize [f_equal s p] to any path with the same endpoint*)
Lemma pi1_transport_nnp {C: UWCwFN} {m n n' : C} (δ : m ~> s n)
  (p : n = n') (sp : s n = s n') 
  : π1 (Logic.transport (λ x , m ~> x) (sp) δ)
    = Logic.transport (λ x , m ~> x) p (π1 δ).
Proof.
  rewrite (UIP_ctx _ _ sp (f_equal s p)).
  apply pi1_transport.
Qed.

Lemma pi2_transport_nnp {C: UWCwFN} {m n n' :C} (δ : m ~> s n)
  (p : n = n') (sp : s n = s n') 
  : π2 (Logic.transport _ sp δ)
    = Logic.transport _ p (π2 δ).
Proof.
  rewrite (UIP_ctx _ _ sp (f_equal s p)).
  apply pi2_transport.
Qed.