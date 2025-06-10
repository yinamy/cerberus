(* theories/Gen_Spec.v: generated lemma specifications from CN *)

Require Import ZArith Bool.
Require CN_Lemmas.CN_Lib.
Require Import CN_Lemmas.CN_Lib_Iris.


Module Types.

  Inductive
    List : Type :=
    | Nil : List
    | Cons : Z -> List -> List.

End Types.


Module Type Parameters.
  Import Types.
  Open Scope Z.
  Parameter Alloc : (Z * Z) -> Prop.


End Parameters.


Module Defs (P : Parameters).
  (* Definitions of functions, structs, and struct ownership predicates *)
  Import Types P.
  Open Scope Z.

  (* Opening Iris mode *)
  Section Defs.
  Context `{!heapGS_gen Σ}.

  Record sllist : Type := { 
  head : Z; 

  tail : Ptr; 
 }.

  Definition Owned_sllist (l: Ptr) (v : sllist) : iProp Σ := Owned_int (CN_Lib_Iris.shift l 0 4) v.(head) ∗ padding (arrayshift l 4 1) 4 ∗ Owned_int (CN_Lib_Iris.shift l 8 8) v.(tail).

  Definition Hd (L : List) :=
    (match L with

 | (Nil) => (0) | (Cons H _) => H end).

  Definition Tl (L : List) :=
    (match L with

 | (Nil) => (Nil) | (Cons _ T) => T end).

  Fixpoint Snoc (Xs : List) (Y : Z) :=
    (match Xs with

 | (Nil) => (Cons Y (Nil)) | (Cons X Zs) => (Cons X (Snoc Zs Y)) end).

  Fixpoint Append (L1 : List) (L2 : List) :=
    (match L1 with

 | (Nil) => L2 | (Cons H T) => (Cons H (Append T L2)) end).


  (* Closing Iris mode *)
  End Defs.

End Defs.


Module ResourcePredicates (P : Parameters).
  Module D := Defs(P).
  Import Types P D.
  Open Scope Z.
  Unset Guard Checking.
  (* Opening Iris mode *)
  Section Iris_Pred_Defs.
  Context `{!heapGS_gen Σ}.

  Fixpoint SLList_At (p : Ptr)  (ret : List) {struct ret}  : iProp Σ := 
(⌜ (p = 0) ⌝  ∧  ⌜ ret = (Nil) ⌝) ∨ (⌜ (Is_true true) ⌝ ∧ ⌜ ~(p = 0) ⌝  ∧ 
∃ (H : sllist),
Owned_sllist p H  ∗ ∃ (T : List), SLList_At H.(tail) T ∗ ⌜ ret = (Cons H.(head) T) ⌝).

  Fixpoint Array (p : Ptr) (n : Z) (ret : List) {struct ret}  : iProp Σ := 
(⌜ (n = (0)) ⌝  ∧  ⌜ ret = (Nil) ⌝) ∨ (⌜ (Is_true true) ⌝ ∧ ⌜ ~(n = (0)) ⌝  ∧ 
∃ (V : Z),
Owned_int p V
 ∗ ∃ (VS : List),
Array (arrayshift p 4 (1)) (CN_Lib.wrapI (-2147483648) 2147483647 (n - (1))) VS ∗ ⌜ ret = (Cons V VS) ⌝).


  (* Closing Iris mode *)
  End Iris_Pred_Defs.
End ResourcePredicates.


Module Lemma_Defs (P : Parameters).
  Module D := Defs(P).
  Module R := ResourcePredicates(P).
  Import Types D P R.
  Open Scope Z.



  (* Opening Iris mode *)
  Section Iris_Type_Defs.
  Context `{!heapGS_gen Σ}.

  Definition each_combine_type : iProp Σ :=
    ∀ (p : Ptr),
∀ (n : Z),
∀ (m : Z),
∀ ( A1 : list Z), each_int  (Z.to_nat (0)) (Z.to_nat (n) - (Z.to_nat (0)))%nat p A1
 -∗ ∀ ( A2 : list Z), each_int  (Z.to_nat n)
(Z.to_nat ((CN_Lib.wrapI (-2147483648) 2147483647 (m + n))) - (Z.to_nat n))%nat p A2
 -∗ ⌜ ((0) <= n) ⌝ -∗ ⌜ (n <= (2147483647)) ⌝ -∗ ⌜ ((0) <= m) ⌝ -∗ ⌜ (m <= (2147483647)) ⌝ -∗ ⌜
((CN_Lib.wrapI (-2147483648) 2147483647 (m + n)) <= (2147483647)) ⌝ -∗ ∃ ( A_post : list Z), each_int 
(Z.to_nat (0)) (Z.to_nat ((CN_Lib.wrapI (-2147483648) 2147483647 (m + n))) -(Z.to_nat (0)))%nat p A_post
 ∧ ⌜ Is_true true ⌝.


  (* Closing Iris mode *)
  End Iris_Type_Defs.
End Lemma_Defs.


Module Type Lemma_Spec (P : Parameters).

  Module L := Lemma_Defs(P).
  Import L.
  (* Opening Iris mode *)
  Section Lemma_Defs.
  Context `{!heapGS_gen Σ}.

  Local Notation "⊢ P" := (⊢@{iPropI Σ} P).

  Parameter each_combine : ⊢ each_combine_type.


  (* Closing Iris mode *)
  End Lemma_Defs.
End Lemma_Spec.


