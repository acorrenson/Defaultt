From defaultt Require Import set.
From Coq Require Import Program.Equality Bool.

Definition Atom : Type := nat.

Inductive Form : Type :=
  | For  : Form -> Form -> Form
  | Fand : Form -> Form -> Form
  | Fneg : Form -> Form
  | Fatm : Atom -> Form
  | Ffalse : Form.

Definition Fimp (fa fb : Form) : Form :=
  For (Fneg fa) fb.

Definition Ftrue : Form :=
  (Fneg Ffalse).

Fixpoint eval (env : nat -> bool) (f : Form) : bool :=
  match f with
  | For fa fb => eval env fa || eval env fb
  | Fand fa fb => eval env fa && eval env fb
  | Fneg fa => negb (eval env fa)
  | Fatm a => env a
  | Ffalse => false
  end.

Definition eval_set (env : nat -> bool) (E : set Form) : Prop :=
  forall f, E f -> eval env f = true.

Definition conseq (E : set Form) (f : Form) : Prop :=
  forall m, eval_set m E -> eval m f = true.

Infix "⊨" := conseq (at level 80).

Inductive deduct : set Form -> Form -> Prop :=
  | and_intro (E : set Form) fa fb :
    deduct E fa -> deduct E fb -> deduct E (Fand fa fb)
  | and_elim_l (E : set Form) fa fb :
    deduct E (Fand fa fb) -> deduct E fa
  | and_elim_r (E : set Form) fa fb :
    deduct E (Fand fa fb) -> deduct E fb
  | neg_elim E fa :
    deduct E fa -> deduct E (Fneg fa) -> deduct E Ffalse
  | bot_elim E fa :
    deduct E Ffalse -> deduct E fa
  | or_intro_l (E : set Form) fa fb :
    deduct E fa -> deduct E (For fa fb)
  | or_intro_r (E : set Form) fa fb :
    deduct E fb -> deduct E (For fa fb)
  | or_elim E fa fb fc :
    deduct E (For fa fb) ->
    deduct E (Fimp fa fc) ->
    deduct E (Fimp fb fc) ->
    deduct E fc
  | excluded_middle E fa :
    deduct E (Fneg (Fand fa (Fneg fa)))
  | axiom (E : set Form) fa : E fa -> deduct E fa.

Infix "⊢" := deduct (at level 80).

Theorem deduct_sound:
  forall E f, E ⊢ f -> E ⊨ f.
Proof.
  intros E f H. induction H; intros m Hm.
  - simpl. now rewrite (IHdeduct1 m Hm), (IHdeduct2 m Hm).
  - specialize (IHdeduct m Hm).
    now apply Bool.andb_true_iff in IHdeduct.
  - specialize (IHdeduct m Hm).
    now apply Bool.andb_true_iff in IHdeduct.
  - specialize (IHdeduct1 m Hm).
    specialize (IHdeduct2 m Hm).
    simpl in *.
    apply Bool.negb_true_iff in IHdeduct2.
    now rewrite IHdeduct1 in IHdeduct2.
  - now specialize (IHdeduct m Hm).
  - specialize (IHdeduct m Hm).
    simpl. rewrite IHdeduct. intuition.
  - specialize (IHdeduct m Hm).
    simpl. rewrite IHdeduct. intuition.
  - specialize (IHdeduct1 m Hm).
    specialize (IHdeduct2 m Hm).
    specialize (IHdeduct3 m Hm).
    simpl in *.
    apply Bool.orb_true_iff in IHdeduct1 as [IHdeduct1 | IHdeduct1].
    + now rewrite IHdeduct1 in IHdeduct2.
    + now rewrite IHdeduct1 in IHdeduct3.
  - simpl. now destruct (eval m fa).
  - now specialize (Hm fa H).
Qed.

(** Deductive closure *)
Definition theory (T : set Form) : set Form :=
  deduct T.

Definition inconsistent (T : set Form) : Prop :=
  deduct T Ffalse.

Definition consistent (T : set Form) : Prop :=
  ~inconsistent T.

Lemma disprove_consistent :
  forall T p, ~deduct T p -> consistent T.
Proof.
  intros T p Hp H.
  now assert (Hcontr : T ⊢ p) by apply bot_elim, H.
Qed.