Require Import Arith Lia List String.

From Eggcc Require Import Lang.

Fixpoint subst (e: Expr) (v : Expr) :=
  match e with
  | Arg => v
  | Single e1 => Single (subst e1 v)
  | Concat e1 e2 => Concat (subst e1 v) (subst e2 v)
  | Boolean b => Boolean b
  | Num n => Num n
  | Add e1 e2 => Add (subst e1 v) (subst e2 v)
  | LessThan e1 e2 => LessThan (subst e1 v) (subst e2 v)
  | Print e1 e2 => Print (subst e1 v) (subst e2 v)
  | If p i t e => If (subst p v) (subst i v) t e
  | DoWhile ei ep eo => DoWhile (subst ei v) ep eo
  (* | CtxInThen ep ei e => CtxInThen ep ei (subst e v)
  | CtxInElse ep ei e => CtxInElse ep ei (subst e v) *)
  | CtxInThen ep ei e => CtxInThen (subst ep v) (subst ei v) (subst e v)
  | CtxInElse ep ei e => CtxInElse (subst ep v) (subst ei v) (subst e v)
  end.

Theorem ss : forall vto e v,
vto ⊢ e ⇓ v ->
( forall a eto ,
  a ⊢ eto ⇓ vto
  ->
  a ⊢ (subst e eto) ⇓ v
  )
.
Proof.
  - intros vto e v H. induction H; intros; simpl; auto.
    * apply ENum.
    * apply EBoolean.
    * apply EAdd; auto.
    * apply ELessThan; auto.
    * apply EPrint; auto.
    * eapply EIfTrue; auto.
    * eapply EIfFalse; auto.
    * eapply EDoWhileTrue; auto.
      + apply H1.
      + apply H2.
    * eapply EDoWhileFalse; auto.
    * eapply ECtxInThen; auto.
      + intuition.
      admit.
Admitted.

Theorem subst_step : forall a0 ei a,
a0 ⊢ ei ⇓ a
->
(forall e v,
a ⊢ e ⇓ v
<->
a0 ⊢ (subst e ei) ⇓ v).
Proof.
  intros a0 ei a H. induction H.
  - intros. split; intros; simpl.
    * admit.
    * admit.
  - intros. split; intros; simpl.
    * admit.
    * admit.
  - admit.
  - intros. split; intros; simpl.
    (* *  *)
    

  (* intros. split.
  - intros. induction H0; simpl.
    * auto.
    * apply ENum.
    * apply EBoolean.
    * apply EAdd; auto.
    * apply ELessThan; auto.
    * apply EPrint; auto.
    * eapply EIfTrue. auto. auto. auto.
    * eapply EIfFalse. auto. auto. auto.
    * eapply EDoWhileTrue; auto.
      + apply H0_1.
      + auto.
    * eapply EDoWhileFalse; auto.
    * eapply ECtxInThen; auto.
      + intuition.
    * apply ECtxInThen with (a0 := a1).
      + auto.
      + auto. specialize (IHBS1 H). apply H0_0. *)
Admitted.

Theorem in_then_allows_pred_true_union : forall a ep ei v,
  a ⊢ CtxInThen (subst ep ei) ei ep ⇓ v
  <->
  a ⊢ CtxInThen (subst ep ei) ei (Boolean true) ⇓ v
.
Proof.
  split.
  - intros. inversion H; subst.
    * eapply ECtxInThen.
      + inversion H. subst.
Admitted.

