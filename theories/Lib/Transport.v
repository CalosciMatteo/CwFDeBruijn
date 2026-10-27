From Stdlib Require Import EqdepFacts.
Require Import Equations.Prop.Logic.
From Category Require Import Lib Theory.

(* This is lemma 2.4.3 from the HoTT Book *)
Lemma homot_naturality
  {A B : Type}
  (f g : A -> B)
  (H: forall x, f x = g x)
  {x y : A}
  (p : x = y)
  : eq_trans (H x) (f_equal g p) = eq_trans (f_equal f p) (H y).
Proof.
  destruct p.
  rewrite eq_trans_refl_l.
  rewrite eq_trans_refl_r.
  reflexivity.
Qed.

Lemma f_equal_id {A : Type} {x y : A} (p:x=y)
  : f_equal Datatypes.id p = p.
Proof.
  destruct p.
  reflexivity.
Qed.

(* This is corollary 2.4. from the HoTT Book *)
Lemma homot_trivial
  {A : Type}
  (f : A -> A)
  (H: forall x, f x = x)
  {x: A}
  : H (f x) = f_equal f (H x).
Proof.
  assert (E:=(f_equal (fun arg => eq_trans arg (eq_sym (H x)))
    (homot_naturality f Datatypes.id H (H x)))).
  cbn in E.
  rewrite <-!(eq_trans_assoc), f_equal_id, eq_trans_sym_inv_r, !eq_trans_refl_r in E.
  exact E.
Qed.

(* This is lemma 2.3.11 from the HoTT Book *)
Lemma transport_funfam
  {A : Type}
  {P Q : A -> Type}
  (f : forall x, P x -> Q x)
  {x y : A}
  (p : x = y)
  (u : P x)
  : Logic.transport Q p (f x u) = f y (Logic.transport P p u).
Proof. now destruct p. Qed.

Lemma transport_prod
  {A : Type}
  {P Q : A -> Type}
  {a a': A}
  {x : P a ∧ Q a}
  (p : a = a')
  : Logic.transport (fun x => P x ∧ Q x) p x =
    (Logic.transport P p (fst x),Logic.transport Q p (snd x)).
Proof.
  destruct p. 
  simpl.
  apply surjective_pairing.
Qed.

Definition homcast {C : Category} {c' d' c d : C}
  (p_c : c' = c) (p_d : d' = d) (f : hom c' d')
  : hom c d
  := (Logic.transport (λ x , x ~> _) p_c
      (Logic.transport (λ x , _ ~> x) p_d f)).

#[global]
Instance proper_homcast {C : Category} {c' d' c d p_c p_d} : (Proper (equiv ==> equiv) (@homcast C c' d' c d p_c p_d)).
Proof.
  unfold homcast.
  proper.
  rewrite X.
  reflexivity.
Qed.

Lemma transport_dom_to_homcast {C : Category} {c c' d : C}
  (p_c : c = c') (f : hom c d)
  : transport (λ x, x ~> d) p_c f = homcast p_c eq_refl f.
Proof.
  destruct p_c.
  reflexivity.
Qed.
Lemma transport_cod_to_homcast {C : Category} {c d d' : C}
  (p_d : d = d') (f : hom c d)
  : transport (λ x, c ~> x) p_d f = homcast eq_refl p_d f.
Proof.
  destruct p_d.
  reflexivity.
Qed.

Lemma transport_domcod_to_coddom {C : Category} {c c' d d' : C}
  (p_c : c = c') (p_d : d = d') (f : hom c d)
  :
  transport (λ x, c' ~> x) p_d (transport (λ x, x ~> d) p_c f) =
  transport (λ x, x ~> d') p_c (transport (λ x, c ~> x) p_d f).
Proof.
  destruct p_c, p_d; reflexivity.
Qed.

Lemma homcast_trans {C : Category} {c'' d'' c' d' c d : C}
  (p_c' : c'' = c') (p_d' : d'' = d') (p_c : c' = c) (p_d : d' = d)
  (f : hom c'' d'')
  : homcast p_c p_d (homcast p_c' p_d' f)
  = homcast (eq_trans p_c' p_c) (eq_trans p_d' p_d) f.
Proof.
  unfold homcast.
  rewrite transport_domcod_to_coddom.
  rewrite !transport_trans.
  reflexivity.
Qed.

Lemma homcast_transport_cod {C : Category} { d'' c' d' d c: C}
  (p_d' : d'' = d') (p_c : c' = c) (p_d : d' = d)
  (f : hom c' d'')
  : homcast p_c p_d (
    transport (λ x, _ ~> x) p_d' f)
  = homcast p_c (eq_trans p_d' p_d) f.
Proof.
  destruct p_c, p_d, p_d'.
  reflexivity.
Qed.

Lemma transport_homcast_cod {C : Category} { d'' c' d' d c: C}
  (p_d' : d'' = d') (p_c : c' = c) (p_d : d' = d)
  (f : hom c' d'')
  : transport (λ x, _ ~> x) p_d (homcast p_c p_d' f)
  = homcast p_c (eq_trans p_d' p_d) f.
Proof.
  destruct p_c, p_d, p_d'.
  reflexivity.
Qed.

Lemma transport_homcast_dom {C : Category} { c'' c' d' d c: C}
  (p_c' : c'' = c') (p_c : c' = c) (p_d : d' = d)
  (f : hom c'' d')
  : transport (λ x, x ~> _) p_c (homcast p_c' p_d f)
  = homcast (eq_trans p_c' p_c) p_d f.
Proof.
  destruct p_c, p_d, p_c'.
  reflexivity.
Qed.

Lemma homcast_rew {C : Category} {c c' d d' : C}
  {p_c' p_c : c' = c} {p_d' p_d : d' = d}
  (e_c : p_c' = p_c) (e_d : p_d' = p_d)
  {f : hom c' d'}
  : homcast p_c' p_d' f = homcast p_c p_d f.
Proof.
  destruct e_c.
  destruct e_d.
  reflexivity.
Qed.
Lemma homcast_UIP {C : Category} {c d : C}
  {p_c : c = c} {p_d : d = d}
  {f : hom c d}
  (UIP: forall (x:C) (e:x=x), e = eq_refl)
  : homcast p_c p_d f = f.
Proof.
  rewrite (UIP _ p_c).
  rewrite (UIP _ p_d).
  reflexivity.
Qed.

Lemma homcast_id {C : Category} {c c' : C} (p: c = c')
  : homcast p p id[c] = id[c'].
Proof.
  rewrite p.
  reflexivity.
Qed.

Lemma homcast_comp {C : Category} {b b' c c' d d' : C}
  (p_b: b = b')
  (p_c: c = c')
  (p_d: d = d')
  (g: b ~> c) (f : c ~> d)
  : homcast p_b p_d (f∘g) = (homcast p_c p_d f) ∘ (homcast p_b p_c g).
Proof.
  destruct p_b, p_c, p_d.
  reflexivity.
Qed.

Lemma homcast_adj {C : Category} {b b' c c' : C}
  (p_b: b = b')
  (p_c: c = c')
  (f: b ~> c) (f': b' ~> c')
  (H : homcast (eq_sym p_b) (eq_sym p_c) f' ≈ f)
  : f' ≈ homcast p_b p_c f.
Proof.
  destruct p_b, p_c; exact H.
Qed.

Lemma homcast_map {C : Category}
  {B1 : C -> C} {D1 : C -> C}
  {B2 : C -> C} {D2 : C -> C}
  {UIP: forall (x:C) (e:x=x), e = eq_refl}
  (map : forall b d, B1(b) ~> D1(d) -> B2(b) ~> D2(d))
  {b d b' d' : C}
  (f: B1 b ~> D1 d)
  (p_b: b = b')
  (p_d: d = d')
  (p_B1: B1 b = B1 b')
  (p_D1: D1 d = D1 d')
  (p_B2: B2 b = B2 b')
  (p_D2: D2 d = D2 d')
  : map _ _ (homcast p_B1 p_D1 f) = (homcast p_B2 p_D2 (map _ _ f)).
Proof.
  destruct p_b, p_d.
  rewrite (UIP _ p_B1).
  rewrite (UIP _ p_D1).
  rewrite (UIP _ p_B2).
  rewrite (UIP _ p_D2).
  reflexivity.
Qed.

Lemma homcast_funfam {C : Category} (P: C->Type)
  {B : C -> C} {D : C -> C}
  {UIP: forall (x:C) (e:x=x), e = eq_refl}
  (map : forall b d, hom (B b) (D d) -> P b)
  {b d b' d' : C}
  (f: B b ~> D d)
  {p_b: b = b'}
  {p_d: d = d'}
  {p_B: B b = B b'}
  {p_D: D d = D d'}
  : map _ _ (homcast p_B p_D f) = (transport P p_b (map _ _ f)).
Proof.
  destruct p_b, p_d.
  rewrite (UIP _ p_B).
  rewrite (UIP _ p_D).
  reflexivity.
Qed.


Lemma eq_trans_invl A (x:A) y z (p : y = z) (q : x = y) (r: x = z)
  : eq_trans q p = r -> p = eq_trans (eq_sym q) r.
Proof.
  intros. destruct q. destruct r. cbn.
  rewrite eq_trans_refl_l in H.
  exact H.
Qed.

Section contraction_to_UIP.
  Context {A : Type} (c : A) (contraction : forall x : A, c = x).

  Lemma contraction_to_prop : forall x y:A, x = y.
  Proof using A c contraction.
    intros ? ?.
    unshelve etransitivity; [exact c|symmetry|]; apply contraction.
  Qed.

  Lemma eq_sym_trans {x y : A} (p : x = y) :
    eq_trans (eq_sym p) p = eq_refl.
  Proof.
    destruct p. reflexivity.
  Qed.

  Lemma contractible_eq_refl {a : A} (p : a = a) : p = eq_refl.
  Proof using A c contraction.
    pose (path_a_to_x := fun x => eq_trans (eq_sym (contraction a)) (contraction x)).
    assert (H_unique : forall (x : A) (q : a = x), q = path_a_to_x x).
    { intros x q.
      destruct q.
      unfold path_a_to_x.
      symmetry.
      apply eq_sym_trans. }
    transitivity (path_a_to_x a).
    - apply H_unique.
    - symmetry. apply H_unique.
  Qed.

  Lemma contraction_to_UIP : UIP_ A.
  Proof using A c contraction.
    intros ? ? ? ?.
    destruct p2.
    apply contractible_eq_refl.
  Qed.
End contraction_to_UIP.