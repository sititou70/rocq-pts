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

(*
  der_absの確認

  ( λn: nat. n ): ( Πn: nat. nat )
  ( λn: nat. n ): ( nat -> nat )

  - absにはprodが付く
  - 引数と引数の型はabsとprodで共通
  - 本体については型付けの関係になる（ここではabs本体のnとprod本体のnatについてn: nat）
  - 略記に関してはLECTURES ON THE CURRY-HOWARD ISOMORPHISM 14.2.1を参照
*)
Example ex1:
  cc
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
      (tm_var "nat")
    ).
Proof with (compute; auto; solve_notin).
  all: apply (der_abs _ _ _ _ _ "*")...
  2: apply (der_prod _ _ "*" _ _ "*" _)...
  all: try apply (der_var _ "*" _ "n")...
  all: try remove_var "n" "*" [(tm_var "nat")].
  all: try apply (der_var _ "□" _ "nat")...
  all: apply der_ax...
Qed.

(*
  der_prodの確認

  ( Πn: nat. nat ): *
  ( nat -> nat ): *

  - prodの型は、prod本体に付く型（ラムダキューブの体系の範囲では）
  - s1、s2、s3がRulesに含まれなければならない
    - s1: prodの引数の型の型
    - s2: prodの本体の型
    - s3: s2と同じ
*)
Example ex2:
  cc
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

(*
  *: □
*)
Example ex3:
  cc
    []
    (tm_sort "*")
    (tm_sort "□").
Proof with (compute; auto; solve_notin).
  all: apply der_ax...
Qed.

(*
  der_prodの確認2

  ( Πn: nat. (Πn: nat. nat) ): *
  ( nat -> nat -> nat ): *

  - 複雑なprodであっても、本体の型がprod自体の型になるという性質から、最終的なprodの本体の型が付く
  - ここでは内側のprodが最終的にnatを返しているので、prod全体にもnatの型である*が付く
*)
Example ex4:
  cc
    [
      ("nat", (tm_sort "*"))
    ]
    (tm_prod
      "n"
      (tm_var "nat")
      (tm_prod
        "n"
        (tm_var "nat")
        (tm_var "nat")
      )
    )
    (tm_sort "*").
Proof with (compute; auto; solve_notin).
  all: apply (der_prod _ _ "*" _ _ "*" _)...
  2: remove_var_prod "n" "*".
  2: apply (der_prod _ _ "*" _ _ "*" _)...
  all: try remove_var "n" "*" [(tm_var "nat")].
  all: try apply (der_var _ "□" _ "nat")...
  all: apply der_ax...
Qed.

(*
  nat -> *

  ( λn: nat. nat ): ( Πn: nat. * )
  ( λn: nat. nat ): ( nat -> * )
*)
Example ex5:
  cc
    [
      ("nat", (tm_sort "*"))
    ]
    (tm_abs
      "n"
      (tm_var "nat")
      (tm_var "nat")
    )
    (tm_prod
      "n"
      (tm_var "nat")
      (tm_sort "*")
    ).
Proof with (compute; auto; solve_notin).
  all: apply (der_abs _ _ _ _ _ "□")...
  all: try remove_var "n" "*" [(tm_var "nat")].
  3: apply (der_prod _ _ "*" _ _ "□" _)...
  all: try remove_var "n" "*".
  all: try apply (der_var _ "□" _ "nat")...
  all: try remove_var "nat" "□".
  all: apply der_ax...
Qed.

(*
  ( Πn: nat. * ): □
  ( nat -> * ): □
*)
Example ex6:
  cc
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

(*
  * -> nat

  ( λA: *. n ): ( ΠA: *. nat )
  ( λA: *. n ): ( * -> nat )
*)
Example ex7:
  cc
    [
      ("nat", (tm_sort "*"));
      ("n", (tm_var "nat"))
    ]
    (tm_abs
      "A"
      (tm_sort "*")
      (tm_var "n")
    )
    (tm_prod
      "A"
      (tm_sort "*")
      (tm_var "nat")
    ).
Proof with (compute; auto; solve_notin).
  all: apply (der_abs _ _ _ _ _ "*")...
  1: try apply (der_var _ "*" _ "n")...
  2: apply (der_prod _ _ "□" _ _ "*" _)...
  all: try remove_var "n" "*".
  all: try apply (der_var _ "□" _ "nat")...
  all: try remove_var "nat" "□".
  all: try remove_var "A" "□".
  all: apply der_ax...
Qed.

(*
  ( ΠA: *. nat ): *
  ( * -> nat ): *
*)
Example ex8:
  cc
    [
      ("nat", (tm_sort "*"));
      ("0", (tm_var "nat"))
    ]
    (tm_prod
      "A"
      (tm_sort "*")
      (tm_var "nat")
    )
    (tm_sort "*").
Proof with (compute; auto; solve_notin).
  all: apply (der_prod _ _ "□" _ _ "*" _)...
  all: try remove_var "0" "*".
  all: try apply (der_var _ "□" _ "nat")...
  all: try remove_var "nat" "□".
  all: try remove_var "A" "□".
  all: apply der_ax...
Qed.

(*
  * -> *

  ( λA: *. nat ): ( ΠA: *. * )
  ( λA: *. nat ): (* -> *)
*)
Example ex9:
  cc
    [
      ("nat", (tm_sort "*"))
    ]
    (tm_abs
      "A"
      (tm_sort "*")
      (tm_var "nat")
    )
    (tm_prod
      "A"
      (tm_sort "*")
      (tm_sort "*")
    ).
Proof with (compute; auto; solve_notin).
  all: apply (der_abs _ _ _ _ _ "□")...
  all: try remove_var "A" "□" [(tm_var "nat")].
  3: apply (der_prod _ _ "□" _ _ "□" _)...
  all: try apply (der_var _ "□" _ "nat")...
  all: try remove_var "nat" "□".
  all: try remove_var "A" "□".
  all: apply der_ax...
Qed.

(*
  ( ΠA: *. * ): □
  (* -> *): □
*)
Example ex10:
  cc
    []
    (tm_prod
      "A"
      (tm_sort "*")
      (tm_sort "*")
    )
    (tm_sort "□").
Proof with (compute; auto; solve_notin).
  all: apply (der_prod _ _ "□" _ _ "□" _)...
  all: try remove_var "A" "□".
  all: apply der_ax...
Qed.

(*
  これまで検査した型付けをまとめる。

  ( λn: nat. n ): ( Πn: nat. nat )
  ( λn: nat. n ): ( nat -> nat )
  ( Πn: nat. nat ): *
  ( nat -> nat ): *
  *: □
  ( Πn: nat. (Πn: nat. nat) ): *
  ( nat -> nat -> nat ): *
  ( λn: nat. nat ): ( Πn: nat. * )
  ( λn: nat. nat ): ( nat -> * )
  ( Πn: nat. * ): □
  ( nat -> * ): □
  ( λA: *. n ): ( ΠA: *. nat )
  ( λA: *. n ): ( * -> nat )
  ( ΠA: *. nat ): *
  ( * -> nat ): *
  ( λA: *. nat ): ( ΠA: *. * )
  ( λA: *. nat ): (* -> *)
  ( ΠA: *. * ): □
  (* -> *): □

  これらを、それが属している対象によって分類してみる。
  ここで、その型が属している対象（型の型）に着目するとわかりやすい。

  # 項（Term）：その型が*に属している

  - λn: nat. n
  - λA: *. n

  # 型（Type）：その型が□に属している

  - Πn: nat. nat
  - nat -> nat
  - Πn: nat. (Πn: nat. nat)
  - nat -> nat -> nat
  - λn: nat. nat
  - ΠA: *. nat
  - * -> nat
  - λA: *. nat

  # カインド（Kind）：それ以外。その型が□そのもの

  - *
  - Πn: nat. *
  - nat -> *
  - ΠA: *. *
  - * -> *

  体系によっては更に上位のsortに属するものも存在する。
*)
