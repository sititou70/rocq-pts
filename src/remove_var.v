Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.Strings.String.
Open Scope string_scope.

Require Import main.
Require Import solve_notin.

Ltac remove_var_rec ct x s :=
  match ct with
    | ?e :: ?ct' =>
      match e with
        | (?e_x, ?e_tm) =>
          match e_x with
            | x =>
              apply (der_weak _ _ e_tm s _ x); compute; auto
            | _ => remove_var_rec ct' x s
          end
        | _ => remove_var_rec ct' x s
      end
    | [] => fail
  end.
Tactic Notation "remove_var" constr(x) constr(s) "[" constr(tm1) constr(tm2) "]" := 
  match goal with
    | |- _ ?ct tm1 tm2 =>
      remove_var_rec ct x s
    | _ => idtac
  end.
Tactic Notation "remove_var" constr(x) constr(s) "[" constr(tm1) "]" :=
  match goal with
    | |- _ ?ct tm1 _ =>
      remove_var_rec ct x s
    | _ => idtac
  end.
Tactic Notation "remove_var" constr(x) constr(s) :=
  match goal with
    | |- _ ?ct _ _ =>
      remove_var_rec ct x s
    | _ => idtac
  end.

Definition stlc :=
  @main.der
    [("*", "□")]
    [
      ("*", "*", "*") (* 項に依存する項 *)
    ].
Example remove_var_rec_ex1:
  stlc
    [
      ("A", (tm_sort "*"));
      ("B", (tm_sort "*"));
      ("C", (tm_sort "*"))
    ]
    (tm_var "B")
    (tm_sort "*").
Proof.
  (* パターンにマッチしない場合は何もしない *)
  remove_var "D" "□".
  remove_var "A" "□" [(tm_var "A")].
  remove_var "A" "□" [(tm_var "B") (tm_sort "□")].

  all: try remove_var "C" "□".
  all: try remove_var "A" "□" [(tm_var "B") (tm_sort "*")].
  all: try remove_var "A" "□" [(tm_sort "*")].
  all: try remove_var "B" "□" [(tm_sort "*")].

  all: try apply (der_var _ "□" _ _); compute; auto.
  all: apply der_ax; simpl; auto.
Qed.

Tactic Notation "remove_var_prod" constr(x) constr(s) :=
  match goal with
    | |- _ ?ct (tm_prod x _ _) _ =>
      remove_var_rec ct x s
    | _ => idtac
  end.
