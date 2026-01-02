Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.Strings.String.
Open Scope string_scope.
Require Import main.

Example subst_ex1:
  subst
    (tm_app
      (tm_var "x")
      (tm_abs
        "y"
        (tm_sort "*")
        (tm_abs
          "x"
          (tm_sort "*")
          (tm_var "x")
        )
      )
    )
    "x"
    (tm_var "z")
  =
  tm_app
    (tm_var "z")
    (tm_abs
      "y"
      (tm_sort "*")
      (tm_abs
        "x"
        (tm_sort "*")
        (tm_var "x")
      )
    ).
Proof.
  compute.
  reflexivity.
Qed.

Example subst_ex2:
  subst
    (tm_app
      (tm_var "x")
      (tm_abs
        "y"
        (tm_sort "*")
        (tm_var "x")
      )
    )
    "x"
    (tm_app
      (tm_var "z")
      (tm_abs
        "y"
        (tm_sort "*")
        (tm_var "y")
      )
    )
  =
  (tm_app
    (tm_app
      (tm_var "z")
      (tm_abs
        "y"
        (tm_sort "*")
        (tm_var "y")
      )
    )
    (tm_abs
      "y"
      (tm_sort "*")
      (tm_app
        (tm_var "z")
        (tm_abs
          "y"
          (tm_sort "*")
          (tm_var "y")
        )
      )
    )
  ).
Proof.
  compute.
  reflexivity.
Qed.

Example subst_ex3:
  subst
    (tm_abs
      "y"
      (tm_sort "*")
      (tm_var "x")
    )
    "x"
    (tm_var "y")
  =
  tm_error "subst: variable capture occurred".
Proof.
  compute.
  reflexivity.
Qed.

Example subst_ex4:
  subst
    (tm_abs
      "y"
      (tm_sort "*")
      (tm_var "z")
    )
    "x"
    (tm_var "y")
  =
  (tm_abs
    "y"
    (tm_sort "*")
    (tm_var "z")
  ).
Proof.
  compute.
  reflexivity.
Qed.
