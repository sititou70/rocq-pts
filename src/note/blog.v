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

(*
  すべての人間は死ぬ
  ソクラテスは人間
  ソクラテスは死ぬ

  Hx：xは人間である（Human）
  Mx：xは死ぬ（Mortal）
*)

Theorem thm6:
  @der
    [("*", "□")]
    [
      ("*", "*", "*"); (* 項に依存する項 *)
      ("*", "□", "□") (* 項に依存する型 *)
    ]
    [
      ("Domain", (tm_sort "*"));
      ("H", (tm_prod "_x" (tm_var "Domain") (tm_sort "*")));
      ("M", (tm_prod "_x" (tm_var "Domain") (tm_sort "*")));
      ("socrates", (tm_var "Domain"))
    ]
    (tm_abs
      "forall_x_Hx_implies_Mx"
      (tm_prod
        "x"
        (tm_var "Domain")
        (tm_prod
          "evid_Hx"
          (tm_app (tm_var "H") (tm_var "x"))
          (tm_app (tm_var "M") (tm_var "x"))
        )
      )
      (tm_abs
        "evid_Hsocrates"
        (tm_app (tm_var "H") (tm_var "socrates"))
        (tm_app
          (tm_app
            (tm_var "forall_x_Hx_implies_Mx")
            (tm_var "socrates")
          )
          (tm_var "evid_Hsocrates")
        )
      )
    )
    (tm_prod
      "forall_x_Hx_implies_Mx"
      (tm_prod
        "x"
        (tm_var "Domain")
        (tm_prod
          "evid_Hx"
          (tm_app (tm_var "H") (tm_var "x"))
          (tm_app (tm_var "M") (tm_var "x"))
        )
      )
      (tm_prod
        "evid_Hsocrates"
        (tm_app (tm_var "H") (tm_var "socrates"))
        (tm_app (tm_var "M") (tm_var "socrates"))
      )
    ).
Proof with (compute; auto 20; solve_notin).
  all: try apply (der_abs _ "forall_x_Hx_implies_Mx" _ _ _ "*")...
  all: try apply (der_abs _ "evid_Hsocrates" _ _ _ "*")...
  1: apply (
    der_app
      _
      _
      "evid_Hx"
      (tm_app (tm_var "H") (tm_var "socrates"))
      (tm_app (tm_var "M") (tm_var "socrates"))
      _
  ).
  1: apply (
    der_app
      _
      _
      "x"
      (tm_var "Domain")
      (tm_prod
        "evid_Hx"
        (tm_app (tm_var "H") (tm_var "x"))
        (tm_app (tm_var "M") (tm_var "x"))
      )
      (tm_var "socrates")
  ).

  all: try apply (der_prod _ _ "*" "forall_x_Hx_implies_Mx" _ "*" _)...
  all: try apply (der_var _ "*" _ "forall_x_Hx_implies_Mx")...
  all: remove_var "forall_x_Hx_implies_Mx" "*".

  all: try apply (der_prod _ _ "*" "x" _ "*" _)...

  all: try apply (der_prod _ _ "*" "evid_Hx" _ "*" _)...
  all: remove_var "evid_Hx" "*".

  all: try apply (der_prod _ _ "*" "evid_Hsocrates" _ "*" _)...
  all: try apply (der_var _ "*" _ "evid_Hsocrates")...
  all: remove_var "evid_Hsocrates" "*".

  all: try apply (der_app _ (tm_var "H") "_x" (tm_var "Domain") (tm_sort "*") _).
  all: try apply (der_var _ "□" _ "H")...
  all: try apply (der_app _ (tm_var "M") "_x" (tm_var "Domain") (tm_sort "*") _).
  all: try apply (der_var _ "□" _ "M")...

  all: remove_var "M" "□".
  all: remove_var "H" "□".

  all: try apply (der_prod _ _ "*" "_x" _ "□" _)...

  all: try apply (der_var _ "*" _ "socrates")...

  all: try apply (der_var _ "*" _ "x")...

  all: remove_var "socrates" "*".
  all: remove_var "x" "*".
  all: remove_var "_x" "*".
  all: try apply (der_var _ "□" _ "Domain")...
  all: remove_var "Domain" "□".
  all: apply der_ax...
Qed.
