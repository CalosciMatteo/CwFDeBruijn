From CwFdeBruijn.Syntax.dB Require Export dB.

Inductive TmP : forall (i : nat) (x : dB), Prop :=
  | TmP_ref i p (Hle : i < p) : TmP p (dB_ref i)
  | TmP_app p x (Hx : TmP p x) y (Hy : TmP p y) : TmP p (dB_app x y)
  | TmP_abs p x (Hx : TmP (S p) x) : TmP p (dB_lam x).

Inductive TmsP : forall (p q : nat) (δ : nat -> dB), Prop :=
  | TmsP_nil p : TmsP p 0 (fun i => dB_ref (p + i))
  | TmsP_snoc {p q : nat} δ (Hδ : TmsP p q δ) x (Hx : TmP p x) :
      TmsP p (S q) (dB_snoc δ x)
  | TmsP_id p : TmsP p p dB_ref
  | TmsP_comp {q r} δ₁ (Hδ₁ : TmsP q r δ₁) {p} δ₂ (Hδ₂ : TmsP p q δ₂) :
    TmsP p r (assign_comp δ₁ δ₂)
  | TmsP_π₁ {p q} δ (Hδ : TmsP p (S q) δ) : TmsP p q (assign_π₁ δ).

Derive Inversion_clear TmP_ref_inversion
  with (forall p i, TmP p (dB_ref i)).

Derive Inversion_clear TmP_app_inversion
  with (forall p x y, TmP p (dB_app x y)).

Derive Inversion_clear TmP_lam_inversion
  with (forall p x, TmP p (dB_lam x)).

Lemma TmP_index {i p} (H : TmP p (dB_ref i)) : i < p.
Proof.
inversion H using TmP_ref_inversion. auto.
Qed.

Lemma TmP_rator {x y p} (H : TmP p (dB_app x y)) : TmP p x.
Proof.
inversion H using TmP_app_inversion. auto.
Qed.

Lemma TmP_rand {x y p} (H : TmP p (dB_app x y)) : TmP p y.
Proof.
inversion H using TmP_app_inversion. auto.
Qed.

Lemma TmP_body {x p} (H : TmP p (dB_lam x)) : TmP (S p) x.
Proof.
inversion H using TmP_lam_inversion. auto.
Qed.

Lemma TmP_reindex {x} : forall {p} (Hx : TmP p x)
  {f} q (Hf : forall i, i < p -> f i < q),
  TmP q (reindex f x).
Proof.
  induction x.
  - simpl.
    intros p Hi f q Hf.
    apply TmP_ref.
    apply Hf.
    apply TmP_index in Hi. assumption.
  - intros p Hx f q Hf.
    simpl.
    apply TmP_app.
    + eapply IHx1.
      * apply TmP_rator in Hx. apply Hx.
      * exact Hf.
    + eapply IHx2.
      * apply TmP_rand in Hx. apply Hx.
      * exact Hf.
  - intros p Hx f q Hf.
  apply TmP_body in Hx.
  simpl. apply TmP_abs.
  eapply IHx.
  + exact Hx.
  + intros [|i].
    * intros _. simpl. lia.
    * intros. simpl. rewrite <-Nat.succ_lt_mono. apply Hf. lia.
Qed.

Lemma TmP_reindex_S {x} : forall {p} (Hx : TmP p x),
  TmP (S p) (reindex S x).
Proof.
  intros.
  eapply TmP_reindex.
  - exact Hx.
  - lia.
Qed.

Lemma TmP_reindex_pred {x} : forall {p} (Hx : TmP (S (S p)) x),
  TmP (S p) (reindex Nat.pred x).
Proof.
  intros.
  eapply TmP_reindex.
  - exact Hx.
  - intros. lia.
Qed.