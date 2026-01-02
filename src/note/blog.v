Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.Strings.String.
Open Scope string_scope.

Require Import main.
Require Import solve_notin.
Require Import remove_var.

(* 「論理学と型システムへ同時に入門してみる」で使う証明 *)

Theorem thm1:
  @der
    [("*", "□")]
    [
      ("*", "*", "*")
    ]
    [
      ("nat", (tm_sort "*"))
    ]
    (tm_prod
      "n"
      (tm_var "nat")
      (tm_var "nat")
    )
    (tm_sort "*").
Proof with (compute; auto; solve_notin).
  all: apply (der_prod _ _ "*" _ _ "*" _)...
  all: try remove_var "n" "*" [(tm_var "nat")].
  all: try apply (der_var _ "□" _ "nat")...
  all: apply der_ax...
Qed.


Theorem thm2:
  @der
    [("*", "□")]
    [
      ("*", "*", "*");
      ("*", "□", "□")
    ]
    [
      ("nat", (tm_sort "*"))
    ]
    (tm_prod
      "n"
      (tm_var "nat")
      (tm_sort "*")
    )
    (tm_sort "□").
Proof with (compute; auto; solve_notin).
  all: apply (der_prod _ _ "*" _ _ "□" _)...
  all: try remove_var "n" "*".
  all: try apply (der_var _ "□" _ "nat")...
  all: try remove_var "nat" "□".
  all: apply der_ax...
Qed.

Theorem thm3:
  @der
    [("*", "□")]
    [
      ("*", "*", "*");
      ("*", "□", "□")
    ]
    [
      ("nat", (tm_sort "*"))
    ]
    (tm_prod
      "n"
      (tm_var "nat")
      (tm_sort "*")
    )
    (tm_sort "□").
Proof with (compute; auto; solve_notin).
  all: apply (der_prod _ _ "*" _ _ "□" _)...
  all: try remove_var "n" "*".
  all: try apply (der_var _ "□" _ "nat")...
  all: try remove_var "nat" "□".
  all: apply der_ax...
Qed.

Theorem thm4:
  @der
    [("*", "□")]
    [
      ("*", "*", "*");
      ("*", "□", "□")
    ]
    [
      ("nat", (tm_sort "*"));
      ("even", (tm_prod "n" (tm_var "nat") (tm_sort "*")));
      ("2", (tm_var "nat"))
    ]
    (tm_app
      (tm_var "even")
      (tm_var "2")
    )
    (tm_sort "*").
Proof with (compute; auto; solve_notin).
  all: apply (der_app _ _ "n" (tm_var "nat") (tm_sort "*") _).
  all: try apply (der_var _ "□" _ "even")...
  all: try remove_var "even" "□".
  all: try apply (der_var _ "*" _ "2")...
  all: try remove_var "2" "*".
  all: try apply (der_prod _ _ "*" _ _ "□" _)...
  all: try remove_var "n" "*".
  all: try apply (der_var _ "□" _ "nat")...
  all: try remove_var "nat" "□".
  all: apply der_ax...
Qed.

Theorem thm5:
  @der
    [("*", "□")]
    [
      ("*", "*", "*");
      ("*", "□", "□")
    ]
    [
      ("nat", (tm_sort "*"));
      ("even", (tm_prod "n" (tm_var "nat") (tm_sort "*")))
    ]
    (tm_prod
      "n"
      (tm_var "nat")
      (tm_app (tm_var "even") (tm_var "n"))
    )
    (tm_sort "*").
Proof with (compute; auto; solve_notin).
  all: apply (der_prod _ _ "*" _ _ "*" _)...
  all: try apply (der_app _ _ "n" (tm_var "nat") (tm_sort "*") _).
  all: try apply (der_var _ "□" _ "even")...
  all: try remove_var "even" "□".
  all: try remove_var_prod "n" "*".
  all: try apply (der_prod _ _ "*" _ _ "□" _)...
  all: try apply (der_var _ "*" _ "n")...
  all: try remove_var "n" "*".
  all: try apply (der_var _ "□" _ "nat")...
  all: try remove_var "nat" "□".
  all: apply der_ax...
Qed.
