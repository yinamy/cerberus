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

  Definition Owned_point (l: Ptr) (v : point) : iProp Σ := Owned_int (shift l 0 4) v.(x) ∗ Owned_int (shift l 4 4) v.(y).


  (* Closing Iris mode *)
  End Struct_Defs.
End Types.


Module Type Parameters.
  Import Types.

  (* no parameters required *)

End Parameters.


Module Defs (P : Parameters).

  Import Types P.
  Open Scope Z.



  (* Opening Iris mode *)
  Section Iris_Type_Defs.
  Context `{!heapGS_gen Σ}.

  Definition struct_lemma_type : iProp Σ :=
    ∀ (p : point),
⌜ (Is_true true) -> (p.(x) = p.(x)) /\ Is_true true ⌝.

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


