Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.Strings.String.
Open Scope string_scope.

Require Import main.
Require Import solve_notin.
Require Import remove_var.

Definition system_u_minus :=
  @main.der
    [
      ("*", "□");
      ("□", "△")
    ]
    [
      ("*", "*", "*");
      ("□", "*", "*");
      ("□", "□", "□");
      ("△", "□", "□")
    ].

Definition arr (S T: tm) := tm_prod "x" S T.
Definition P (S: tm) := arr S (tm_sort "*").
Definition all (x: var) (S chi: tm) := tm_prod x S chi.
Definition bot := all "p" (tm_sort "*") (tm_var "p").
Definition not (phi: tm) := arr phi bot.
Definition lam (x: var) (xt t: tm) := tm_abs x xt t.
Definition Lam (chi: var) (c: tm) := lam chi (tm_sort "□") c.
Definition app (b T: tm) := tm_app b T.
Definition suppose (n: var) (phi P: tm) := lam n phi P.
Definition Let (x: var) (S P: tm) := lam x S P.

Definition U :=
  tm_prod
    "chi"
    (tm_sort "□")
    (arr
      (arr
        (P (P (tm_var "chi")))
        (tm_var "chi")
      )
      (P (P (tm_var "chi")))
    ).

Definition tau (t: tm) :=
  Lam
    "chi"
    (lam
      "f"
      (P (P (tm_var "chi")))
      (lam
        "p"
        (P (tm_var "chi"))
        (app
          t
          (lam
            "x"
            U
            (app
              (tm_var "p")
              (app
                (tm_var "f")
                (app (app (tm_var "x") (tm_var "chi")) (tm_var "f"))
              )
            )
          )
        )
      )
    ).

Definition sigma (s: tm) :=
  app
    (app s U)
    (lam
      "t"
      (P (P U))
      (tau (tm_var "t"))
    ).

Definition delta :=
  lam
    "y"
    U
    (not
      (all
        "p"
        (P U)
        (arr
          (app (sigma (tm_var "y")) (tm_var "p"))
          (app (tm_var "p") (tau (sigma (tm_var "y"))))
        )
      )
    ).

Definition omega :=
  tau
    (lam
      "p"
      (P U)
      (all
        "x"
        U
        (arr
          (app (sigma (tm_var "x")) (tm_var "p"))
          (app (tm_var "p") (tm_var "x"))
        )
      )
    ).
