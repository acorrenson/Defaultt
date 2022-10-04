From defaultt Require Import lprop set.
From Coq Require Import List.

Record default : Type := {
  d_pre : Form;
  d_just : list Form;
  d_conc : Form;
  d_just_wf : length d_just >= 1;
}.

(** Default Theories *)
Record DT := {
  W : set Form;
  D : set default;
}.

(** Fixpoint Characterization of DT Extensions *)
Module Fix.

(** Properties of the Γ operator *)
Record GammaRules (dt : DT) (S S' : set Form) : Prop := {
  gamma_W         : W dt ⊆ S';
  gamma_closed_1  : S' ≡ theory S';
  gamma_closed_2  :
    forall d, D dt d -> S' (d_pre d) ->
    (forall j, In j (d_just d) -> ~(S (Fneg j))) ->
    S' (d_conc d)
}.

(** Γ(S) is defined as the smalles set satisfying [GammaRules] *)
Definition GammaOp (dt : DT) (S : set Form) : set Form :=
  smallest (GammaRules dt S).

(** An extensions is a fixpoint of the Γ operator *)
Definition Extension (dt : DT) (E : set Form) : Prop :=
  E ≡ GammaOp dt E.

End Fix.

(** 'Sequential' Characterization of DT Extensions *)
Module Seq.

Definition Extension (dt : DT) (E : set Form) : Prop :=
  False (* TODO *).

End Seq.

(** The fixpoint and the sequential characterization are equivalent *)
Theorem Extension_Fix_Seq:
  forall dt, Fix.Extension dt ≡ Seq.Extension dt.
Proof.
  (* TODO *)
Admitted.
