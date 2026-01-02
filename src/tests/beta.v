Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.Strings.String.
Open Scope string_scope.

Require Import main.
Require Import solve_notin.
Require Import remove_var.

Example beta1_appabs_ex:
  beta1
    (tm_app
      (tm_abs
        "x"
        (tm_sort "*")
        (tm_var "x")
      )
      (tm_var "y")
    )
    (tm_var "y").
Proof.
  eauto using beta1.
Qed.

Example beta1_app1_ex:
  beta1
    (tm_app
      (tm_app
        (tm_abs
          "x"
          (tm_sort "*")
          (tm_var "x")
        )
        (tm_var "f")
      )
      (tm_var "arg")
    )
    (tm_app
      (tm_var "f")
      (tm_var "arg")
    ).
Proof.
  eauto using beta1.
Qed.

Example beta1_app2_ex:
  beta1
    (tm_app
      (tm_var "f")
      (tm_app
        (tm_abs
          "x"
          (tm_sort "*")
          (tm_var "x")
        )
        (tm_var "arg")
      )
    )
    (tm_app
      (tm_var "f")
      (tm_var "arg")
    ).
Proof.
  eauto using beta1.
Qed.

Example beta1_abs_xt_ex:
  beta1
    (tm_abs
      "x"
      (tm_app
        (tm_abs
          "x"
          (tm_sort "*")
          (tm_var "x")
        )
        (tm_var "nat")
      )
      (tm_var "x")
    )
    (tm_abs
      "x"
      (tm_var "nat")
      (tm_var "x")
    ).
Proof.
  eauto using beta1.
Qed.

Example beta1_abs_t_ex:
  beta1
    (tm_abs
      "x"
      (tm_var "nat")
      (tm_app
        (tm_abs
          "x"
          (tm_sort "*")
          (tm_var "x")
        )
        (tm_var "x")
      )
    )
    (tm_abs
      "x"
      (tm_var "nat")
      (tm_var "x")
    ).
Proof.
  eauto using beta1.
Qed.

Example beta1_prod_xt_ex:
  beta1
    (tm_prod
      "x"
      (tm_app
        (tm_abs
          "x"
          (tm_sort "*")
          (tm_var "x")
        )
        (tm_var "nat")
      )
      (tm_var "x")
    )
    (tm_prod
      "x"
      (tm_var "nat")
      (tm_var "x")
    ).
Proof.
  eauto using beta1.
Qed.

Example beta1_prod_t_ex:
  beta1
    (tm_prod
      "x"
      (tm_var "nat")
      (tm_app
        (tm_abs
          "x"
          (tm_sort "*")
          (tm_var "x")
        )
        (tm_var "x")
      )
    )
    (tm_prod
      "x"
      (tm_var "nat")
      (tm_var "x")
    ).
Proof.
  eauto using beta1.
Qed.

Example beta_step_ex:
  beta
    (tm_var "y")
    (tm_app
      (tm_abs
        "x"
        (tm_sort "*")
        (tm_var "x")
      )
      (tm_var "y")
    ).
Proof.
  eauto using beta, beta1.
Qed.

Example beta_refl_ex:
  beta
    (tm_var "x")
    (tm_var "x").
Proof.
  eauto using beta.
Qed.

Example beta_sym_ex:
  beta
    (tm_var "y")
    (tm_app
      (tm_abs
        "x"
        (tm_sort "*")
        (tm_var "x")
      )
      (tm_var "y")
    ).
Proof.
  eauto using beta, beta1.
Qed.

Example beta_trans_ex:
  beta
    (tm_app
      (tm_abs
        "x"
        (tm_sort "*")
        (tm_app
          (tm_abs
            "x"
            (tm_sort "*")
            (tm_var "x")
          )
          (tm_var "x")
        )
      )
      (tm_var "x")
    )
    (tm_var "x").
Proof.
  eapply
    (beta_trans
      _
      (tm_app
        (tm_abs
          "x"
          (tm_sort "*")
          (tm_var "x")
        )
        (tm_var "x")
      )
    ).
  eauto using beta, beta1.
  eauto using beta, beta1.
Qed.

Definition der :=
  @main.der
    [("*", "□")]
    [
      ("*", "*", "*"); (* 項に依存する項 *)
      ("□", "*", "*"); (* 型に依存する項 *)
      ("*", "□", "□"); (* 項に依存する型 *)
      ("□", "□", "□")  (* 型に依存する型 *)
    ].

Example conv_ex1:
  der
    [
      ("nat", (tm_sort "*"))
    ]
    (tm_abs
      "n"
      (tm_var "nat")
      (tm_var "n")
    )
    (tm_prod
      "n"
      (tm_var "nat")
      (tm_app
        (tm_abs
          "A"
          (tm_sort "*")
          (tm_var "A")
        )
        (tm_var "nat")
      )
    ).
Proof with (compute; auto; solve_notin).
  apply (der_conv _ _ (tm_prod "n" (tm_var "nat") (tm_var "nat")) _ "*").
  1: eauto using beta1, beta.
  1: apply (der_abs _ _ _ _ _ "*")...
  2, 3: apply (der_prod _ _ "*" _ _ "*" _)...
  5: apply (der_app _ _ "A" (tm_sort "*") (tm_sort "*") _).
  5: apply (der_abs _ _ _ _ _ "□")...
  6: apply (der_prod _ _ "□" _ _ "□" _)...

  all: try apply (der_var _ "*" _ "n")...

  all: try remove_var "n" "*" [(tm_var "A")].
  all: try remove_var "nat" "□" [(tm_var "A")].

  all: try remove_var "A" "□" [(tm_var "nat")].
  all: try remove_var "n" "*" [(tm_var "nat")].

  all: try remove_var "A" "□" [(tm_sort "*")].
  all: try remove_var "n" "*" [(tm_sort "*")].
  all: try remove_var "nat" "□" [(tm_sort "*")].

  all: try apply (der_var _ "□" _ "nat")...
  all: try apply (der_var _ "□" _ "A")...

  all: apply der_ax...
Qed.
