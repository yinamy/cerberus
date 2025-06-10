(* theories/Gen_Spec.v: generated lemma specifications from CN *)

Require Import ZArith Bool.
Require CN_Lemmas.CN_Lib.
Require Import CN_Lemmas.CN_Lib_Iris.


Module Types.

  (* Opening Iris mode *)
  Section Struct_Defs.
  Context `{!heapGS_gen Σ}.

  Record point : Type := { 
  x : Z; 

  y : Z; 
 }.

  Definition Owned_point (l: Ptr) (v : point) : iProp Σ := 
    Owned_int (CN_Lib_Iris.shift l 0 1) v.(x) 
    ∗ padding (arrayshift l 1 1) 3 
    ∗ Owned_int (CN_Lib_Iris.shift l 4 4) v.(y).


  (* Closing Iris mode *)
  End Struct_Defs.
End Types.


Module Type Parameters.
  Import Types.

  (* no parameters required *)

End Parameters.


Module ResourcePredicates (P : Parameters).
  Import Types P.

  (* Opening Iris mode *)
  Section Iris_Pred_Defs.
  Context `{!heapGS_gen Σ}.

  Definition Alloc  (ret_ty : (Z * Z)) : Prop := 
unsupported: uninterpreted predicate


  (* Closing Iris mode *)
  End Iris_Pred_Defs.
End ResourcePredicates.


Module Defs (P : Parameters).

  Import Types P.
  Open Scope Z.



  (* Opening Iris mode *)
  Section Iris_Type_Defs.
  Context `{!heapGS_gen Σ}.

  Definition struct_lemma_type : iProp Σ :=
    ∀ (p : Ptr),
∀ (P : point),
Owned_point p P  -∗ ∃ (P_post : point), Owned_point p P_post  ∗ ⌜ P = P_post ⌝ ∧ emp.

  Definition resource_lemma_type : iProp Σ :=
    ∀ (p : Ptr),
∀ (v1 : Z),
Owned_int p v1  -∗ ⌜ v1 = (0) ⌝ → ∃ (v2 : Z), Owned_int p v2  ∗ ⌜ v2 = (0) ⌝ ∧ emp.


  (* Closing Iris mode *)
  End Iris_Type_Defs.
End Defs.


Module Type Lemma_Spec (P : Parameters).

  Module D := Defs(P).
  Import D.
  (* Opening Iris mode *)
  Section Lemma_Defs.
  Context `{!heapGS_gen Σ}.

  Local Notation "⊢ P" := (⊢@{iPropI Σ} P).

  Parameter struct_lemma : ⊢ struct_lemma_type.

  Parameter resource_lemma : ⊢ resource_lemma_type.


  (* Closing Iris mode *)
  End Lemma_Defs.
End Lemma_Spec.


