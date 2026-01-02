Require Import Stdlib.Lists.List.
Import ListNotations.

Ltac solve_notin_rec :=
  match goal with
    | H: ?P \/ ?Q |- _ =>
        destruct H;
        try solve [inversion H];
        try solve [solve_notin_rec H]
    | H: _ |- _ => try solve [inversion H]
  end.
Tactic Notation "solve_notin" :=
  try solve [
    simpl;
    unfold Logic.not;
    intro;
    solve_notin_rec
  ].
Example solve_notin_example1:
  ~ (In 0 [ 1; 2; 3; 4; 5 ]).
Proof. solve_notin. Qed.
