Definition IsHSet (X : Type) : Prop
  := forall (x y : X) (p q : x = y), p = q.

Lemma hset_hOneType : forall X : Type,
    IsHSet X -> forall (x y : X) (p q : x = y), unit.
Proof.
  intros X f x y p q.
  pose (fun a => f x y p a) as g.
  assert (forall a (r : q = a), eq_trans (g q) r = g a).
  { intros. destruct a. subst q. reflexivity. }
  constructor.
Qed.
