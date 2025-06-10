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

  Record queue : Type := { 
  front : Ptr; 

  back : Ptr; 
 }.

  Definition Owned_queue (l: Ptr) (v : queue) : iProp Σ := Owned_int (CN_Lib_Iris.shift l 0 8) v.(front) ∗ Owned_int (CN_Lib_Iris.shift l 8 8) v.(back).

  Record queue_cell : Type := { 
  first : Z; 

  next : Ptr; 
 }.

  Definition Owned_queue_cell (l: Ptr) (v : queue_cell) : iProp Σ := Owned_int (CN_Lib_Iris.shift l 0 4) v.(first) ∗ padding (arrayshift l 4 1) 4 ∗ Owned_int (CN_Lib_Iris.shift l 8 8) v.(next).

  Definition Hd (L : List) :=
    (match L with

 | (Nil) => (0) | (Cons H _) => H end).

  Definition Tl (L : List) :=
    (match L with

 | (Nil) => (Nil) | (Cons _ T) => T end).

  Fixpoint Snoc (Xs : List) (Y : Z) :=
    (match Xs with

 | (Nil) => (Cons Y (Nil)) | (Cons X Zs) => (Cons X (Snoc Zs Y)) end).


  (* Closing Iris mode *)
  End Defs.
  (* Opening Iris mode *)
  Unset Guard Checking.

  Section Iris_Pred_Defs.
  Context `{!heapGS_gen Σ}.

  Fixpoint SLList_At (p : Ptr)  (ret : List) {struct ret}  : iProp Σ := 
(⌜ (p = 0) ⌝  ∧  ⌜ ret = (Nil) ⌝) ∨ (⌜ (Is_true true) ⌝ ∧ ⌜ ~(p = 0) ⌝  ∧ 
∃ (H : sllist),
Owned_sllist p H  ∗ ∃ (T : List), SLList_At H.(tail) T ∗ ⌜ ret = (Cons H.(head) T) ⌝).

  Fixpoint QueueAux (f : Ptr) (b : Ptr) (ret : List) {struct ret}  : iProp Σ := 
(⌜ (f = b) ⌝  ∧  ⌜ ret = (Nil) ⌝) ∨ (⌜ (Is_true true) ⌝ ∧ ⌜ ~(f = b) ⌝  ∧ 
∃ (F : queue_cell),
Owned_queue_cell f F
 ∗ ⌜ (~ (F.(next) = 0)) ⌝ ∗ ⌜ ((F.(next) = b) ∨ (~ (F.(next) = b))) ⌝ ∗ ∃ (B : List),
QueueAux F.(next) b B ∗ ⌜ ret = (Cons F.(first) B) ⌝).

  Fixpoint QueueFB (front : Ptr) (back : Ptr) (ret : List) {struct ret}  : iProp Σ := 
(⌜ (front = 0) ⌝  ∧  ⌜ ret = (Nil) ⌝) ∨ (⌜ (Is_true true) ⌝ ∧ ⌜ ~(front = 0) ⌝  ∧ 
∃ (B : queue_cell),
Owned_queue_cell back B
 ∗ ⌜ (B.(next) = 0) ⌝ ∗ ⌜ ((front = back) ∨ (~ (front = back))) ⌝ ∗ ∃ (L : List),
QueueAux front back L ∗ ⌜ ret = (Snoc L B.(first)) ⌝).

  Fixpoint QueuePtr_At (q : Ptr)  (ret : List) {struct ret}  : iProp Σ := 
(⌜ (Is_true true) ⌝  ∧ 
∃ (Q : queue),
Owned_queue q Q
 ∗ ⌜ (((Q.(front) = 0) ∧ (Q.(back) = 0)) ∨ ((~ (Q.(front) = 0)) ∧ (~ (Q.(back) = 0)))) ⌝ ∗ ∃ (L : List),
QueueFB Q.(front) Q.(back) L ∗ ⌜ ret = L ⌝).


  (* Closing Iris mode *)
  End Iris_Pred_Defs.
End Defs.


Module Lemma_Defs (P : Parameters).
  Module D := Defs(P).
  Import Types D P.
  Open Scope Z.



  (* Opening Iris mode *)
  Section Iris_Type_Defs.
  Context `{!heapGS_gen Σ}.

  Definition push_lemma_type : iProp Σ :=
    ∀ (front : Ptr), ∀ (p : Ptr),
    ⌜ ((front = p) ∨ (~ (front = p))) ⌝ -∗ 
    ∀ (Q : List), QueueAux front p Q -∗ 
    ∀ (P : queue_cell), Owned_queue_cell p P -∗ 
  ⌜ (~ (P.(next) = 0)) ⌝ -∗ 
  ⌜ ((front = P.(next)) ∨ (~ (front = P.(next)))) ⌝ ∧ 
  ∃ (Q_post : List), QueueAux front P.(next) Q_post ∗ 
  ⌜ (Q_post = (Snoc Q P.(first))) ⌝ ∧ emp.


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

  Parameter push_lemma : ⊢ push_lemma_type.


  (* Closing Iris mode *)
  End Lemma_Defs.
End Lemma_Spec.


