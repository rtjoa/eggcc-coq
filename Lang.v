Require Import Arith Lia List String.

Inductive Expr : Type :=
| Arg: Expr
| Single: Expr -> Expr
| Concat: Expr -> Expr -> Expr
| Num: nat -> Expr
| Boolean: bool -> Expr
| Add: Expr -> Expr -> Expr
| LessThan: Expr -> Expr -> Expr
| Print : Expr -> Expr -> Expr
(* pred in then else*)
| If : Expr -> Expr -> Expr -> Expr -> Expr
(* in pred out *)
| DoWhile : Expr -> Expr -> Expr -> Expr
(* pred in e *)
| CtxInThen : Expr -> Expr -> Expr -> Expr
(* pred in e *)
| CtxInElse : Expr -> Expr -> Expr -> Expr
.

Inductive Typ : Type :=
| TInt: Typ
| TState: Typ
| TTuple: list Type -> Typ.

Record State := 
{
  (* For now, only nats can be stored
    addr -> option nat *)
  Mem: list (nat * option nat);
  Log: list nat
}.

Inductive Value : Type :=
| VNum: nat -> Value
| VBoolean: bool -> Value
| VTuple: list Value -> Value
| VState: State -> Value.

Definition initstate :=
  (VState {| Mem := nil; Log := nil |}).

(* Big-step judgement *)
Inductive BS : Value -> Expr -> Value -> Prop :=
| EArg : forall a,
  BS a Arg a
| ENum : forall a n,
  BS a (Num n) (VNum n)
| EBoolean : forall a b,
  BS a (Boolean b) (VBoolean b)
| EAdd : forall a e1 e2 n1 n2,
  BS a e1 (VNum n1) ->
  BS a e2 (VNum n2) ->
  BS a (Add e1 e2) (VNum (n1 + n2))
| ELessThan : forall a e1 e2 n1 n2,
  BS a e1 (VNum n1) ->
  BS a e2 (VNum n2) ->
  BS a (LessThan e1 e2) (VBoolean (Nat.ltb n1 n2))
| EPrint : forall a estate mem log e n,
  BS a estate (VState {| Mem := mem; Log := log |}) ->
  BS a e (VNum n) ->
  BS a (Print estate e) (VState {| Mem := mem; Log := cons n log|})
| EIfTrue : forall a ep ei et ee vi vt,
  BS a ep (VBoolean true) ->
  BS a ei vi ->
  BS vi et vt ->
  BS a (If ep ei et ee) vt
| EIfFalse : forall a ep ei et ee vi ve,
  BS a ep (VBoolean false) ->
  BS a ei vi ->
  BS vi ee ve ->
  BS a (If ep ei et ee) ve
| EDoWhileTrue : forall a ei ep eo vi vo vfin,
  BS a ei vi ->
  BS vi ep (VBoolean true) ->
  BS vi eo vo ->
  BS vo (DoWhile Arg ep eo) vfin ->
  BS a (DoWhile ei ep eo) vfin
| EDoWhileFalse : forall a ei ep eo vi vo,
  BS a ei vi ->
  BS vi ep (VBoolean false) ->
  BS vi eo vo ->
  BS a (DoWhile ei ep eo) vo
| ECtxInThen : forall a ei ep e v a0,
  BS a e v ->
  BS a0 ei a ->
  BS a0 ep (VBoolean true) ->
  BS a (CtxInThen ep ei e) v
| ECtxInElse : forall a ei ep e v a0,
  BS a e v ->
  BS a0 ei a ->
  BS a0 ep (VBoolean false) ->
  BS a (CtxInElse ep ei e)v
.

Notation "A ⊢ B ⇓ C" := (BS A B C) (at level 80).
(* | even_SS : forall n, even n -> even (S (S n)). *)

Lemma lookup_app :
(VNum 0) ⊢ (DoWhile (Arg) (LessThan (Arg) (Num 2)) (Add (Arg) (Num 1))) ⇓ (VNum 3).
Proof.
  eapply EDoWhileTrue.
  - eapply EArg.
  - apply ELessThan with (e1 := Arg) (e2 := Num 2) (n1 := 0) (n2 := 2).
    + apply EArg.
    + apply ENum.
  - apply EAdd with (e1 := Arg) (e2 := Num 1) (n1 := 0) (n2 := 1).
    + apply EArg.
    + apply ENum.
  - simpl. eapply EDoWhileTrue.
    -- eapply EArg.
    -- apply ELessThan with (e1 := Arg) (e2 := Num 2) (n1 := 1) (n2 := 2).
      + apply EArg.
      + apply ENum.
    -- apply EAdd with (e1 := Arg) (e2 := Num 1) (n1 := 1) (n2 := 1).
      + apply EArg.
      + apply ENum.
    -- simpl. eapply EDoWhileFalse.
      --- eapply EArg.
      --- apply ELessThan with (e1 := Arg) (e2 := Num 2) (n1 := 2) (n2 := 2).
        + apply EArg.
        + apply ENum.
      --- apply EAdd with (e1 := Arg) (e2 := Num 1) (n1 := 2) (n2 := 1).
        + apply EArg.
        + apply ENum.
Qed.

Theorem introduce_if_ctx : forall a ep ei et ee v,
  a ⊢ If ep ei et ee ⇓ v
  <->
  a ⊢ If ep ei (CtxInThen ep ei et) (CtxInElse ep ei ee) ⇓ v
.
Proof.
  split. 
  - intros.
    * inversion H.
      + eapply EIfTrue; auto.
        -- apply H7.
        -- eapply ECtxInThen; auto.
          ** apply H7.
          ** auto.
      + eapply EIfFalse; auto.
        -- apply H7.
        -- eapply ECtxInElse; auto.
          ** apply H7.
          ** auto.
  - intros. inversion H.
    * eapply EIfTrue; auto.
      + apply H7.
      + inversion H8; auto.
    * eapply EIfFalse; auto.
      + apply H7.
      + inversion H8; auto.
Qed.

Theorem ctx_allows_const_union : forall a ep n v,
  a ⊢ CtxInThen ep (Num n) Arg ⇓ v
  <->
  a ⊢ CtxInThen ep (Num n) (Num n) ⇓ v
.
Proof.
  split.
  - intros. inversion H.
    * eapply ECtxInThen.
      + subst. inversion H6. subst. inversion H4. subst. apply ENum.
      + subst. inversion H6. subst. inversion H4. subst. apply ENum.
      + subst. apply H7.
  - intros. inversion H.
    * eapply ECtxInThen.
      + subst. inversion H6. subst. inversion H4. subst. apply EArg.
      + subst. inversion H6. subst. inversion H4. subst. apply ENum.
      + subst. apply H7. 
Qed.
