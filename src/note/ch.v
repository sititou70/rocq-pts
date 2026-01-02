Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.Strings.String.
Open Scope string_scope.

Require Import main.
Require Import solve_notin.
Require Import remove_var.

Definition cc :=
  @main.der
    [("*", "□")]
    [
      ("*", "*", "*"); (* 項に依存する項 *)
      ("□", "*", "*"); (* 型に依存する項 *)
      ("*", "□", "□"); (* 項に依存する型 *)
      ("□", "□", "□")  (* 型に依存する型 *)
    ].

Theorem thm1:
  cc
    [
      ("A", (tm_sort "*"))
    ]
    (tm_abs
      "a"
      (tm_var "A")
      (tm_var "a")
    )
    (tm_prod
      "a"
      (tm_var "A")
      (tm_var "A")
    ).
Proof with (compute; auto; solve_notin).
  all: apply (der_abs _ _ _ _ _ "*")...
  all: try apply (der_prod _ _ "*" "a" _ "*" _)...
  1: apply (der_var _ "*" _ _)...
  all: remove_var "a" "*".
  all: apply (der_var _ "□" _ _)...
  all: apply der_ax...
Qed.

Definition bot: tm :=
  tm_prod
    "P"
    (tm_sort "*")
    (tm_var "P").

Definition not (P: tm) :=
  tm_prod
    "p"
    P
    bot.

Theorem thm2:
  cc
    [
      ("D", (tm_sort "*"));
      ("A", (tm_sort "*"))
    ]
    (tm_abs
      "d"
      (tm_var "D")
      (tm_abs
        "not d"
        (not (tm_var "D"))
        (tm_app
          (tm_app
            (tm_var "not d")
            (tm_var "d")
          )
          (tm_var "A")
        )
      )
    )
    (tm_prod
      "d"
      (tm_var "D")
      (tm_prod
        "not d"
        (not (tm_var "D"))
        (tm_var "A")
      )
    ).
Proof with (compute; auto; solve_notin).
  apply (der_abs _ _ _ _ _ "*")...
  1: apply (der_abs _ _ _ _ _ "*")...
  1: apply (der_app _ _ "P" (tm_sort "*") (tm_var "P") _).
  1: apply (der_app _ _ "p" (tm_var "D") (tm_prod "P" (tm_sort "*") (tm_var "P")) _).

  all: try apply (der_prod _ _ "*" "d" _ "*" _)...
  all: try apply (der_prod _ _ "*" "not d" _ "*" _)...

  all: try apply (der_var _ "*" _ "not d")...
  all: remove_var "not d" "*".

  all: try apply (der_prod _ _ "*" "p" _ "*" _)...
  all: try apply (der_prod _ _ "□" "P" _ "*" _)...

  all: try apply (der_var _ "□" _ "P")...

  all: try apply (der_var _ "*" _ "p")...
  all: remove_var "p" "*".

  all: try apply (der_var _ "*" _ "d")...
  all: remove_var "d" "*".

  all: remove_var "D" "□" [(tm_var "A")].
  all: try apply (der_var _ "□" _ "A")...

  all: remove_var "A" "□" [(tm_var "D")].
  all: try apply (der_var _ "□" _ "D")...

  all: remove_var "D" "□".
  all: remove_var "A" "□".
  all: apply der_ax...
Qed.

Definition or (A B: tm): tm :=
  tm_prod
    "P"
    (tm_sort "*")
    (tm_prod
      "_ap"
      (tm_prod "a" A (tm_var "P"))
      (tm_prod
        "_bp"
        (tm_prod "b" B (tm_var "P"))
        (tm_var "P")
      )
    ).

Theorem thm3:
  cc
    [
      ("A", (tm_sort "*"));
      ("B", (tm_sort "*"))
    ]
    (tm_abs
      "A or B"
      (or (tm_var "A") (tm_var "B"))
      (tm_abs
        "not A"
        (not (tm_var "A"))
        (tm_app
          (tm_app
            (tm_app
              (tm_var "A or B")
              (tm_var "B")
            )
            (tm_abs
              "a"
              (tm_var "A")
              (tm_app
                (tm_app
                  (tm_var "not A")
                  (tm_var "a")
                )
                (tm_var "B")
              )
            )
          )
          (tm_abs
            "b"
            (tm_var "B")
            (tm_var "b")
          )
        )
      )
    )
    (tm_prod
      "A or B"
      (or (tm_var "A") (tm_var "B"))
      (tm_prod
        "not A"
        (not (tm_var "A"))
        (tm_var "B")
      )
    ).
Proof with (compute; auto; solve_notin).
  all: try apply (der_abs _ "A or B" _ _ _ "*")...
  all: try apply (der_abs _ "not A" _ _ _ "*")...

  all: try apply (der_prod _ _ "*" "A or B" _ "*" _)...
  1: apply (
    der_app
      _
      _
      "_bp"
      (tm_prod "b" (tm_var "B") (tm_var "B"))
      (tm_var "B")
      _
  ).
  1: apply (
    der_app
      _
      _
      "_ap"
      (tm_prod "a" (tm_var "A") (tm_var "B"))
      (tm_prod
        "_bp"
        (tm_prod "b" (tm_var "B") (tm_var "B"))
        (tm_var "B")
      )
      _
  ).
  1: apply (
    der_app
      _
      _
      "P"
      (tm_sort "*")
      (tm_prod
        "_ap"
        (tm_prod "a" (tm_var "A") (tm_var "P"))
        (tm_prod
          "_bp"
          (tm_prod "b" (tm_var "B") (tm_var "P"))
          (tm_var "P")
        )
      )
      (tm_var "B")
  ).
  all: try apply (der_var _ "*" _ "A or B")...
  all: remove_var "A or B" "*".

  all: try apply (der_abs _ "a" _ _ _ "*")...
  all: try apply (der_app _ ((tm_app (tm_var "not A") (tm_var "a"))) "P" (tm_sort "*") (tm_var "P") _).
  all: try apply (der_app _ (tm_var "not A") "p" (tm_var "A") (tm_prod "P" (tm_sort "*") (tm_var "P")) _).

  all: try apply (der_prod _ _ "*" "not A" _ "*" _)...
  all: try apply (der_var _ "*" _ "not A")...
  all: remove_var "not A" "*".

  all: try apply (der_abs _ "b" _ _ _ "*")...

  all: try apply (der_prod _ _ "*" "p" _ "*" _)...
  all: remove_var "p" "*".
  all: try apply (der_prod _ _ "□" "P" _ "*" _)...
  all: try apply (der_prod _ _ "*" "_ap" _ "*" _)...
  all: remove_var "_ap" "*".
  all: try apply (der_prod _ _ "*" "_bp" _ "*" _)...
  all: remove_var "_bp" "*".
  all: try apply (der_prod _ _ "*" "a" _ "*" _)...
  all: try apply (der_prod _ _ "*" "b" _ "*" _)...

  all: try apply (der_var _ "*" _ "a")...
  all: remove_var "a" "*".
  all: try apply (der_var _ "*" _ "b")...
  all: remove_var "b" "*".

  all: remove_var "A" "□" [(tm_var "P")].
  all: remove_var "B" "□" [(tm_var "P")].
  all: remove_var "P" "□" [(tm_var "A")].
  all: remove_var "B" "□" [(tm_var "A")].
  all: remove_var "P" "□" [(tm_var "B")].
  all: remove_var "A" "□" [(tm_var "B")].

  all: try apply (der_var _ "□" _ _)...

  all: remove_var "P" "□".
  all: remove_var "A" "□".
  all: remove_var "B" "□".
  all: apply der_ax...
Qed.
