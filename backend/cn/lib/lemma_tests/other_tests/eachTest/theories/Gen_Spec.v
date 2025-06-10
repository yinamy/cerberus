(* theories/Gen_Spec.v: generated lemma specifications from CN *)

Require Import ZArith Bool.
Require CN_Lemmas.CN_Lib.
Require Import CN_Lemmas.CN_Lib_Iris.


Module Types.

  (* no type definitions required *)

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

(* no struct definitions required *)

  (* Closing Iris mode *)
  End Defs.

End Defs.


Module ResourcePredicates (P : Parameters).
  Module D := Defs(P).
  Import Types P D.
  Open Scope Z.
  (* no resource predicates required *)

End ResourcePredicates.


Module Lemma_Defs (P : Parameters).
  Module D := Defs(P).
  Module R := ResourcePredicates(P).
  Import Types D P R.
  Open Scope Z.



  (* Opening Iris mode *)
  Section Iris_Type_Defs.
  Context `{!heapGS_gen Σ}.

  Definition array_lemma_type : iProp Σ :=
    ∀ (p : Ptr),
∀ (n : Z),
∀ (i : Z),
∀ ( l_A : list Z), let A := (fix eachI (j n : nat) (p : Ptr) (l : list Z) := 
            (match n with
              | O => emp%I
              | S n' => (Owned_int p (nth j%nat l 0) ∗
                        eachI (S j) n' (arrayshift p 4 1) l)%I
              end))
(Z.to_nat 0) (Z.to_nat n) p l_A in A  -∗ ∃ (A_post : Z), Owned_int p A_post  ∧ emp.


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

  Parameter array_lemma : ⊢ array_lemma_type.


  (* Closing Iris mode *)
  End Lemma_Defs.
End Lemma_Spec.


