Definition set T : Type := T -> Prop.

Definition subseteq {T} (a b : set T) : Prop :=
  forall x, a x -> b x.

Definition seteq {T} (a b : set T) : Prop :=
  subseteq a b /\ subseteq b a.

Definition union {T} (a b : set T) : set T :=
  fun x => a x \/ b x.

Definition inter {T} (a b : set T) : set T :=
  fun x => a x /\ b x.

Definition i_union {T} (f : nat -> set T) : set T :=
  fun x => exists i, f i x.

Definition i_inter {T} (f : nat -> set T) : set T :=
  fun x => forall i, f i x.

Definition smallest {T} (f : set (set T)) : set T :=
  fun x => forall S, f S -> S x.

Definition add {T} (a : set T) (t : T) :=
  fun x => a x \/ x = t.

Infix "∩" := inter (at level 80).
Infix "∪" := union (at level 80).
Infix "≡" := seteq (at level 80).
Infix "⊆" := subseteq (at level 80).