Notation bar := $(exact I)$.
Notation foo := bar (only parsing).
Class baz := { x : False }.
Global Instance: baz.
Admitted.
Definition baz0 := ((_ : baz) = (_ : baz)).
Definition foo1 := (foo = foo).
Fail Definition baz1 := prod ((_ : baz) = (_ : baz)) (foo = foo).
