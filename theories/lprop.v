From defaultt Require Import set.
From Coq Require Import Program.Equality.

Definition Atom : Type := nat.

Inductive Form : Type :=
  | Fand : Form -> Form -> Form
  | Fneg : Form -> Form
  | Fatm : Atom -> Form
  | Ffalse : Form.

Record rule : Type := {
  r_pre : Form;
  r_conc : Form;
}.

Inductive deduct' (R : set rule) : set Form -> Form -> Prop :=
  | and_intro' (E : set Form) fa fb :
    deduct' R E fa -> deduct' R E fb -> deduct' R E (Fand fa fb)
  | and_elim_l' (E : set Form) fa fb :
    deduct' R E (Fand fa fb) -> deduct' R E fa
  | and_elim_r' (E : set Form) fa fb :
    deduct' R E (Fand fa fb) -> deduct' R E fb
  | neg_elim' E fa fb :
    deduct' R E fa -> deduct' R E (Fneg fa) -> deduct' R E fb
  | excluded_middle' E fa :
    deduct' R E (Fneg (Fand fa (Fneg fa)))
  | axiom' (E : set Form) fa : E fa -> deduct' R E fa
  | app_rule E fa fb :
    deduct' R E fa -> R (Build_rule fa fb) -> deduct' R E fb.

Definition deduct T f := deduct' (fun _ => False) T f.

(** Deductive closure *)
Definition th (T : set Form) : set Form :=
  deduct T.

(** Deductive closure with additional rules *)
Definition th' (R : set rule) (T : set Form) : set Form :=
  deduct' R T.