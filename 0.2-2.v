Section tautology.
  Variable T : Set.
  Variable x : T.
  Variable p : T -> Prop.
  Variable q : T -> T -> Prop.
  Variable f : T -> T.

  Theorem a : p x -> (forall x, p x -> exists y, q x y) -> (forall x y, q x y -> q y (f y)) -> exists z, q z (f z).
    intros.
    assert (exists y : T, q x y).
    apply (H0 x H).
    destruct H2.
    assert (q x0 (f x0)).
    apply (H1 x x0 H2).
    exists x0.
    assumption.
  Qed.
End tautology.
