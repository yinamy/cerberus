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

  Fixpoint Snoc (Xs : List) (Y : Z) :=
    (match Xs with

 | (Nil) => (Cons Y (Nil)) | (Cons X Zs) => (Cons X (Snoc Zs Y)) end).

  Definition push_lemma_type : Prop :=
    forall (front : CN_Lib.Loc),
forall (p : CN_Lib.Loc),
((front = p) \/ (~ (front = p))) -> Unsupported term.

End Defs.


Module Type Lemma_Spec (P : Parameters).

  Module D := Defs(P).
  Import D.

  Parameter push_lemma : push_lemma_type.

End Lemma_Spec.


