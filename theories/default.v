From defaultt Require Import lprop set.
From Coq Require Import List.

Record default : Type := {
  d_pre : Form;
  d_just : list Form;
  d_conc : Form;
  d_just_wf : length d_just >= 1;
}.


Definition reduct (D : set default) (E : set Form) : set rule :=
  fun (r : rule) =>
    exists just just_wf,
      D (Build_default (r_pre r) just (r_conc r) just_wf) /\
      forall j, In j just -> ~E (Fneg j).

Definition formify (R : set rule) : set Form :=
  fun f =>
    exists r, R r /\ f = Fand (r_pre r).

Definition Extension (D : set default) (W : set Form) (E : set Form) : Prop :=
  seteq _ E (th' (reduct D E) (union _ W (reduct D E))).



