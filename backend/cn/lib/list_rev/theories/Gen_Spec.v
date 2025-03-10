(* theories/Gen_Spec.v: generated lemma specifications from CN *)

Require Import ZArith Bool.
Require CN_Lemmas.CN_Lib.


Module Types.

  Inductive
    List : Type :=
    | Nil : List
    | Cons : Z -> List -> List.

End Types.


Module Type Parameters.
  Import Types.

  (* no parameters required *)

End Parameters.


Module Defs (P : Parameters).

  Import Types P.
  Open Scope Z.

  Definition Hd (L : List) :=
    (match L with

 | (Nil) => (0) | (Cons H _) => H end).

  Definition Tl (L : List) :=
    (match L with

 | (Nil) => (Nil) | (Cons _ T) => T end).

  Fixpoint Append (L1 : List) (L2 : List) :=
    (match L1 with

 | (Nil) => L2 | (Cons H T) => (Cons H (Append T L2)) end).

  Fixpoint Snoc (Xs : List) (Y : Z) :=
    (match Xs with

 | (Nil) => (Cons Y (Nil)) | (Cons X Zs) => (Cons X (Snoc Zs Y)) end).

  Fixpoint RevList (L : List) :=
    (match L with

 | (Nil) => (Nil) | (Cons H T) => (Snoc (RevList T) H) end).

  Definition Append_Nil_RList_type : Prop :=
    forall (L1 : List),
(Is_true true) -> ((Append L1 (Nil)) = L1) /\ Is_true true.

  Definition Append_Cons_RList_type : Prop :=
    forall (L1 : List),
forall (X : Z),
forall (L2 : List),
(Is_true true) -> ((Append L1 (Cons X L2)) = (Append (Snoc L1 X) L2)) /\ Is_true true.

End Defs.


Module Type Lemma_Spec (P : Parameters).

  Module D := Defs(P).
  Import D.

  Parameter Append_Nil_RList : Append_Nil_RList_type.

  Parameter Append_Cons_RList : Append_Cons_RList_type.

End Lemma_Spec.


