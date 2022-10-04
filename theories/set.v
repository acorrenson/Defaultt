Definition set T : Type := T -> Prop.

Definition seteq T (a b : set T) :=
  forall x, (a x <-> b x).

  Definition union T (a b : set T) :=
  fun x => a x \/ b x.