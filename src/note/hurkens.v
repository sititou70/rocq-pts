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
