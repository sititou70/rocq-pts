Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.Strings.String.
Open Scope string_scope.

Require Import main.
Require Import solve_notin.
Require Import remove_var.

(*
  単純型付きラムダ計算
  命題論理
*)
Definition stlc :=
  @main.der
    [("*", "□")]
    [
      ("*", "*", "*") (* 項に依存する項 *)
    ].
Theorem stlc_thm:
  stlc
    [("nat", (tm_sort "*"))]
    (tm_abs
      "x"
      (tm_var "nat")
      (tm_var "x")
    )
    (tm_prod
      "x"
      (tm_var "nat")
      (tm_var "nat")
    ).
Proof with (compute; auto; solve_notin).
  all: apply (der_abs _ _ _ _ _ "*")...
  2: apply (der_prod _ _ "*" _ _ "*" _)...
  1: apply (der_var _ "*" _ _)...
  3: remove_var "x" "*".
  all: apply (der_var _ "□" _ _)...
  all: apply der_ax...
Qed.

(*
  System F
  2階命題論理

  - 項に依存する項
  - 型に依存する項
*)
Definition system_f :=
  @main.der
    [("*", "□")]
    [
      ("*", "*", "*"); (* 項に依存する項 *)
      ("□", "*", "*")  (* 型に依存する項 *)
    ].
Theorem system_f_thm:
  system_f
    []
    (tm_abs
      "a"
      (tm_sort "*")
      (tm_abs
        "x"
        (tm_var "a")
        (tm_var "x")
      )
    )
    (tm_prod
      "a"
      (tm_sort "*")
      (tm_prod
        "x"
        (tm_var "a")
        (tm_var "a")
      )
    ).
Proof with (compute; auto; solve_notin).
  all: apply (der_abs _ _ _ _ _ "*")...
  1: apply (der_abs _ _ _ _ _ "*")...
  3: apply (der_prod _ _ "□" _ _ "*" _)...
  2, 4: apply (der_prod _ _ "*" _ _ "*" _)...
  1: apply (der_var _ "*" _ _)...
  3, 5: remove_var "x" "*".
  all: try apply (der_var _ "□" _ "a")...
  all: apply der_ax...
Qed.

(*
  Logical Framework (LF)
  述語論理
*)
Definition lambda_p :=
  @main.der
    [("*", "□")]
    [
      ("*", "*", "*"); (* 項に依存する項 *)
      ("*", "□", "□")  (* 項に依存する型 *)
    ].
Theorem lambda_p_thm:
  lambda_p
    [
      ("nat", (tm_sort "*"));
      ("vec", (tm_prod "_" (tm_var "nat") (tm_sort "*")))
    ]
    (tm_abs
      "n"
      (tm_var "nat")
      (tm_abs
        "v"
        (tm_app
          (tm_var "vec")
          (tm_var "n")
        )
        (tm_var "v")
      )
    )
    (tm_prod
      "n"
      (tm_var "nat")
      (tm_prod
        "v"
        (tm_app
          (tm_var "vec")
          (tm_var "n")
        )
        (tm_app
          (tm_var "vec")
          (tm_var "n")
        )
      )
    ).
Proof with (compute; auto; solve_notin).
  all: apply (der_abs _ _ _ _ _ "*")...
  1: apply (der_abs _ _ _ _ _ "*")...
  1: apply (der_var _ "*" _ _)...
  3: apply (der_prod _ _ "*" _ _ "*" _)...
  2, 4: apply (der_prod _ _ "*" _ _ "*" _)...
  3, 5: remove_var "v" "*".
  all: try apply (der_app _ _ "_" (tm_var "nat") (tm_sort "*") _).
  all: try apply (der_var _ "□" _ "vec")...
  all: remove_var "vec" "□".
  all: try apply (der_prod _ _ "*" "_" _ "□" _)...
  all: try apply (der_var _ "*" _ "n")...
  all: remove_var "n" "*".
  all: remove_var "_" "*".
  all: try apply (der_var _ "□" _ "nat")...
  all: remove_var "nat" "□".
  all: apply der_ax...
Qed.

(*
  \lambda \underline{\omega}
  弱高階命題論理
*)
Definition lambda_underline_omega :=
  @main.der
    [("*", "□")]
    [
      ("*", "*", "*"); (* 項に依存する項 *)
      ("□", "□", "□")  (* 型に依存する型 *)
    ].
Theorem lambda_underline_omega_thm:
  lambda_underline_omega
    []
    (tm_abs
      "a"
      (tm_sort "*")
      (tm_prod
        "x"
        (tm_var "a")
        (tm_var "a")        
      )
    )
    (tm_prod
      "a"
      (tm_sort "*")
      (tm_sort "*")
    ).
Proof with (compute; auto; solve_notin).
  all: apply (der_abs _ _ _ _ _ "□")...
  1: apply (der_prod _ _ "*" _ _ "*" _)...
  3: apply (der_prod _ _ "□" _ _ "□" _)...
  2: remove_var "x" "*".
  all: try apply (der_var _ "□" _ "a")...
  5: remove_var "a" "□".
  all: apply der_ax...
Qed.

(*
  Calculus of Construction (CC)
  高階述語論理
*)
Definition cc :=
  @main.der
    [("*", "□")]
    [
      ("*", "*", "*"); (* 項に依存する項 *)
      ("□", "*", "*"); (* 型に依存する項 *)
      ("*", "□", "□"); (* 項に依存する型 *)
      ("□", "□", "□")  (* 型に依存する型 *)
    ].
Definition leibniz_eq (A x y: tm): tm :=
  tm_prod
    "P"
    (tm_prod "_a" A (tm_sort "*"))
    (tm_prod
      "_px"
      (tm_app (tm_var "P") x)
      (tm_app (tm_var "P") y)
    ).
Definition eq_ind_term: tm :=
  tm_abs
    "A"
    (tm_sort "*")
    (tm_abs
      "P"
      (tm_prod "_a" (tm_var "A") (tm_sort "*"))
      (tm_abs
        "x"
        (tm_var "A")
        (tm_abs
          "Px"
          (tm_app (tm_var "P") (tm_var "x"))
          (tm_abs
            "y"
            (tm_var "A")
            (tm_abs
              "eqxy"
              (leibniz_eq (tm_var "A") (tm_var "x") (tm_var "y"))
              (tm_app (tm_app (tm_var "eqxy") (tm_var "P")) (tm_var "Px"))
            )
          )
        )
      )
    ).
Definition eq_ind_type: tm :=
  tm_prod
    "A"
    (tm_sort "*")
    (tm_prod
      "P"
      (tm_prod "_a" (tm_var "A") (tm_sort "*"))
      (tm_prod
        "x"
        (tm_var "A")
        (tm_prod
          "Px"
          (tm_app (tm_var "P") (tm_var "x"))
          (tm_prod
            "y"
            (tm_var "A")
            (tm_prod
              "eqxy"
              (leibniz_eq (tm_var "A") (tm_var "x") (tm_var "y"))
              (tm_app (tm_var "P") (tm_var "y"))
            )
          )
        )
      )
    ).
Theorem cc_thm:
  cc
    []
    eq_ind_term
    eq_ind_type.
Proof with (compute; auto 10; solve_notin).
  unfold eq_ind_term, eq_ind_type.

  (* termのabsを処理 *)
  all: apply (der_abs _ "A" _ _ _ "*")...
  1: apply (der_abs _ "P" _ _ _ "*")...
  1: apply (der_abs _ "x" _ _ _ "*")...
  1: apply (der_abs _ "Px" _ _ _ "*")...
  1: apply (der_abs _ "y" _ _ _ "*")...
  1: apply (der_abs _ "eqxy" _ _ _ "*")...

  (* termのappを処理 *)
  1: apply (der_app _ _ "_px" (tm_app (tm_var "P") (tm_var "x")) (tm_app (tm_var "P") (tm_var "y")) _).
  1: apply (
    der_app
      _
      _
      "P"
      (tm_prod "_a" (tm_var "A") (tm_sort "*"))
      (tm_prod "_px" (tm_app (tm_var "P") (tm_var "x")) (tm_app (tm_var "P") (tm_var "y")))
      (tm_var "P")
  ).

  (* absの処理によって発生したprodを処理 *)
  all: try apply (der_prod _ _ "□" "A" _ "*" _)...
  all: try apply (der_prod _ _ "□" "P" _ "*" _)...
  all: try apply (der_prod _ _ "*" "x" _ "*" _)...
  all: try apply (der_prod _ _ "*" "Px" _ "*" _)...
  all: try apply (der_prod _ _ "*" "y" _ "*" _)...
  all: try apply (der_prod _ _ "*" "eqxy" _ "*" _)...

  (* 残りのprodを処理 *)
  all: remove_var "Px" "*" [(tm_prod "P" (tm_prod "_a" (tm_var "A") (tm_sort "*")) (tm_prod "_px" (tm_app (tm_var "P") (tm_var "x")) (tm_app (tm_var "P") (tm_var "y")))) ].
  all: try apply (der_app _ _ "_a" (tm_var "A") (tm_sort "*") _).
  all: remove_var_prod "P" "□".
  all: try apply (der_prod _ _ "□" "P" _ "*" _)...
  all: try apply (der_prod _ _ "*" "_a" _ "□" _)...
  all: try apply (der_prod _ _ "*" "_px" _ "*" _)...
  all: remove_var "_px" "*".
  all: try apply (der_app _ _ "_a" (tm_var "A") (tm_sort "*") _).

  (* 
    この時点で、すべてのゴールの結論が以下のようになっている

    - der _ (tm_var _) _
    - der _ (tm_sort _) _

    以降は、変数を導入した逆順に処理していき、最後にsortを公理で示す。

    ただし、新たに生まれる変数やsortのサブゴールは、後続の証明で処理されるためそのままにしておく。

    ゴールの数が膨大になるため、以下のコマンドによって、残りのゴールの項の種類を確認しながら進める。

    cbpaste | tr -d "\n" | grep -o -P "\] ?\(.*?\)" | sed -e "s/\] /\]/" | sort | uniq
  *)

  (* (tm_var "eqxy")を処理する *)
  all: try apply (der_var _ "*" _ "eqxy")...
  all: remove_var "eqxy" "*".
  all: remove_var "Px" "*" [(tm_prod "P" (tm_prod "_a" (tm_var "A") (tm_sort "*")) (tm_prod "_px" (tm_app (tm_var "P") (tm_var "x")) (tm_app (tm_var "P") (tm_var "y"))))].
  all: remove_var_prod "P" "□".
  all: try apply (der_prod _ _ "□" "P" _ "*" _)...
  all: try apply (der_prod _ _ "*" "_a" _ "□" _)...
  all: try apply (der_prod _ _ "*" "_px" _ "*" _)...
  all: remove_var "_px" "*" [(tm_app (tm_var "P") (tm_var "y"))].
  all: try apply (der_app _ _ "_a" (tm_var "A") (tm_sort "*") _).

  (* (tm_var "y")を処理する *)
  all: try apply (der_var _ "*" _ "y")...
  all: try remove_var "y" "*".

  (* (tm_var "Px")を処理する *)
  all: try apply (der_var _ "*" _ "Px")...
  all: try remove_var "Px" "*".
  all: try apply (der_app _ _ "_a" (tm_var "A") (tm_sort "*") _).

  (* (tm_var "x")を処理する *)
  all: try apply (der_var _ "*" _ "x")...
  all: try remove_var "x" "*".

  (* (tm_var "P")を処理する *)
  all: try apply (der_var _ "□" _ "P")...
  all: remove_var "P" "□".
  all: try apply (der_prod _ _ "*" "_a" _ "□" _)...

  (* (tm_var "A")を処理する *)
  all: try remove_var "_a" "*".
  all: try apply (der_var _ "□" _ "A")...
  all: try remove_var "A" "□".

  (* (tm_sort "*")を処理する *)
  all: try apply der_ax...
Qed.
