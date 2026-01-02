Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.Strings.String.
Open Scope string_scope.

Definition sort := string.

Definition var := string.

Inductive tm: Type :=
  | tm_var: var -> tm
  | tm_sort: sort -> tm
  | tm_app: tm -> tm -> tm
  | tm_abs: var -> tm -> tm -> tm
  | tm_prod: var -> tm -> tm -> tm
  | tm_error: string -> tm.
Definition tm_dec (t1 t2: tm) : {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality; apply string_dec.
Defined.

Fixpoint fv (t: tm): list string :=
  match t with
    | tm_var x => [x]
    | tm_sort _ => []
    | tm_app t1 t2 => (fv t1) ++ (fv t2)
    | tm_abs x xt t => (fv xt) ++ (remove string_dec x (fv t))
    | tm_prod x xt t => (fv xt) ++ (remove string_dec x (fv t))
    | tm_error _ => []
  end.

(* 
  see: LECTURES ON THE CURRY-HOWARD ISOMORPHISM 1.2.4
  だたし、この代入の定義はCCではなくラムダ計算のものであることに注意する
  特に、ラムダ項や依存積項に対しては、変数束縛の一般的な観点によって定義を拡張している。
*)
Fixpoint subst (t: tm) (from: var) (to: tm): tm :=
  match t with
    | tm_var x => if String.eqb x from then to else t
    | tm_sort _ => t
    | tm_app t1 t2 => tm_app (subst t1 from to) (subst t2 from to)
    | tm_abs x xt t =>
        if
          String.eqb x from
        then
          (tm_abs x (subst xt from to) t)
        else
          if
            (* 代入が定義される条件は「x ∉ FV(to)なるλxtにおけるfromの自由な出現が無い場合」である *)
            orb
              (* x ∉ FV(to)かどうかにかかわらず、そもそもλxtにおけるfromの自由な出現が無いため、代入は定義される *)
              (negb (existsb (String.eqb from) (fv t)))
              (* 
                λxtにおけるfromの自由な出現があるが、そのλxtについてx ∉ FV(to)ではないため、代入は定義される
                ここでは(subst t from to)の結果はそのままtになるが、エラーにならずに評価を進めるために必要な条件である
              *)
              (negb (existsb (String.eqb x) (fv to)))
          then 
            (tm_abs x (subst xt from to) (subst t from to))
          else
            tm_error "subst: variable capture occurred"
    | tm_prod x xt t =>
        if
          String.eqb x from
        then
          (tm_prod x (subst xt from to) t)
        else
          if
            orb
              (negb (existsb (String.eqb from) (fv t)))
              (negb (existsb (String.eqb x) (fv to)))
          then 
            (tm_prod x (subst xt from to) (subst t from to))
          else
            tm_error "subst: variable capture occurred"
    | tm_error _ => t
  end.

Inductive beta1: tm -> tm -> Type :=
  | beta1_appabs:
    forall (t1_x: var) (t1_tx t1_t t2: tm),
    beta1 (tm_app (tm_abs t1_x t1_tx t1_t) t2) (subst t1_t t1_x t2)
  | beta1_app1:
    forall (t1 t1' t2: tm),
    beta1 t1 t1' ->
    beta1 (tm_app t1 t2) (tm_app t1' t2)
  | beta1_app2:
    forall (t1 t2 t2': tm),
    beta1 t2 t2' ->
    beta1 (tm_app t1 t2) (tm_app t1 t2')
  | beta1_abs_xt:
    forall (x: var) (xt xt' t: tm),
    beta1 xt xt' ->
    beta1 (tm_abs x xt t) (tm_abs x xt' t)
  | beta1_abs_t:
    forall (x: var) (xt t t': tm),
    beta1 t t' ->
    beta1 (tm_abs x xt t) (tm_abs x xt t')
  | beta1_prod_xt:
    forall (x: var) (xt xt' t: tm),
    beta1 xt xt' ->
    beta1 (tm_prod x xt t) (tm_prod x xt' t)
  | beta1_prod_t:
    forall (x: var) (xt t t': tm),
    beta1 t t' ->
    beta1 (tm_prod x xt t) (tm_prod x xt t')
    .
Inductive beta: tm -> tm -> Type :=
  | beta_step:
    forall (t1 t2: tm),
    beta1 t1 t2 ->
    beta t1 t2
  | beta_refl:
    forall (t: tm),
    beta t t
  | beta_sym:
    forall (t1 t2: tm),
    beta t2 t1 ->
    beta t1 t2
  | beta_trans:
    forall (t1 t2 t3: tm),
    beta t1 t2 ->
    beta t2 t3 ->
    beta t1 t3.

Definition ctx_entry: Type := (var * tm).
Definition ctx := list ctx_entry.
Definition empty_ctx: ctx := [].
Definition extend_ctx (ct: ctx) (e: ctx_entry): ctx := e :: ct.
Definition ctx_dom (ct: ctx): list var := map fst ct.
Definition ctx_entry_dec (e1 e2: ctx_entry) : {e1 = e2} + {e1 <> e2}.
Proof.
  decide equality.
  apply tm_dec.
  apply string_dec.
Defined.

(* see: LECTURES ON THE CURRY-HOWARD ISOMORPHISM Chapter 14 *)
Definition axiom: Type := sort * sort.
Definition rule: Type := sort * sort * sort.
Inductive der {Axioms: list axiom} {Rules: list rule}: ctx -> tm -> tm -> Type :=
  | der_ax:
    forall (s1 s2: sort),
    In (s1, s2) Axioms ->
    der [] (tm_sort s1) (tm_sort s2)
  | der_var:
    forall (A: tm) (s: sort) (ct': ctx) (x: var),
    let ct := remove ctx_entry_dec (x, A) ct' in
    (* ~ (In x (ctx_dom ct)) -> *) (* 型付け規則および、extendのnotationの定義から必要だが、removeによって保証される *)
    (In (x, A) ct') ->
    der ct A (tm_sort s) ->
    der ct' (tm_var x) A
  | der_prod:
    forall (ct: ctx) (A: tm) (s1: sort) (x: var) (B: tm) (s2 s3: sort),
    In (s1, s2 ,s3) Rules ->
    der ct A (tm_sort s1) ->
    der (extend_ctx ct (x, A)) B (tm_sort s2) ->
    ~ (In x (ctx_dom ct)) -> (* extendのnotationの定義より。Chapter 3.1を参照 *)
    der ct (tm_prod x A B) (tm_sort s3)
  | der_abs:
    forall (ct: ctx) (x: var) (A B C: tm) (s: sort),
    der (extend_ctx ct (x, A)) B C ->
    ~ (In x (ctx_dom ct)) -> (* extendのnotationの定義より。Chapter 3.1を参照 *)
    der ct (tm_prod x A C) (tm_sort s) ->
    der ct (tm_abs x A B) (tm_prod x A C)
  | der_app:
    forall (ct: ctx) (A: tm) (x: var) (B C D: tm),
    der ct A (tm_prod x B C) ->
    der ct D B ->
    der ct (tm_app A D) (subst C x D)
  | der_weak:
    forall (A B C: tm) (s: sort) (ct': ctx) (x: var),
    let ct := remove ctx_entry_dec (x, C) ct' in 
    (* ~ (In x (ctx_dom ct)) -> *) (* 型付け規則および、extendのnotationの定義から必要だが、removeによって保証される *)
    (In (x, C) ct') ->
    der ct A B ->
    der ct C (tm_sort s) ->
    der ct' A B
  | der_conv:
    forall (ct: ctx) (A B B': tm) (s: sort),
    beta B B' ->
    der ct A B ->
    der ct B' (tm_sort s) ->
    der ct A B'.
