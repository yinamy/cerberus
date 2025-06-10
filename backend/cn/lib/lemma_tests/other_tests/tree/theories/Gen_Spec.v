(* theories/Gen_Spec.v: generated lemma specifications from CN *)

Require Import ZArith Bool.
Require CN_Lemmas.CN_Lib.
Require Import CN_Lemmas.CN_Lib_Iris.


Module Types.

  Inductive
    tree_list : Type :=
    | Empty_List : tree_list
    | Cons_List : tree -> tree_list -> tree_list
    with
    tree : Type :=
    | Empty_Tree : tree
    | Node : tree_list -> Z -> tree.

End Types.


Module Type Parameters.
  Import Types.
  Open Scope Z.
  Parameter array_to_tree_list : ((Z -> tree)) -> Z -> tree_list.

  Parameter default_children : ((Z -> tree)).

  Parameter in_tree : tree -> (((Z -> Z)) * Z * Z) -> bool.

  Parameter tree_v : tree -> (((Z -> Z)) * Z * Z) -> Z.

  Parameter nth_tree_list : tree_list -> Z -> tree.

  Parameter Alloc : (Z * Z) -> Prop.


End Parameters.


Module Defs (P : Parameters).
  (* Definitions of functions, structs, and struct ownership predicates *)
  Import Types P.
  Open Scope Z.

  (* Opening Iris mode *)
  Section Defs.
  Context `{!heapGS_gen Σ}.


  Definition tree_v_step (t : tree) (arc : (((Z -> Z)) * Z * Z)) :=
    (match t with

 | (Empty_Tree) => (0)
| (Node children v) =>
(let arc2 := ((fst (fst arc)), (CN_Lib.wrapI (-2147483648) 2147483647 ((snd (fst arc)) + (1))), (snd arc)) in (if
((snd (fst arc)) <? (snd arc)) then (tree_v (nth_tree_list children ((fst (fst arc)) (snd (fst arc)))) arc2) else v)) end).

  Definition in_tree_step (t : tree) (arc : (((Z -> Z)) * Z * Z)) :=
    (match t with

 | (Empty_Tree) => false
| (Node children v) =>
(let arc2 := ((fst (fst arc)), (CN_Lib.wrapI (-2147483648) 2147483647 ((snd (fst arc)) + (1))), (snd arc)) in (if
((snd (fst arc)) <? (snd arc)) then (in_tree (nth_tree_list children ((fst (fst arc)) (snd (fst arc)))) arc2) else true))
end).


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

  Definition in_tree_tree_v_lemma_type : iProp Σ :=
    ∀ (t : tree),
∀ (arc : (((Z -> Z)) * Z * Z)),
∀ (t_children : ((Z -> tree))),
⌜ ((0) <= (snd (fst arc))) ⌝ -∗ ⌜ ((snd arc) <= (65536)) ⌝ -∗ ⌜ ((tree_v t arc) = (tree_v_step t arc)) ⌝ ∧ ⌜
((in_tree t arc) = (in_tree_step t arc)) ⌝ ∧ (let i := ((fst (fst arc)) (snd (fst arc))) in ⌜
(if (((0) <=? i) && (i <? (16))) then ((nth_tree_list (array_to_tree_list t_children (16)) i) = (t_children i)) else
(Is_true true)) ⌝ ∧ ⌜ Is_true true ⌝).


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

  Parameter in_tree_tree_v_lemma : ⊢ in_tree_tree_v_lemma_type.


  (* Closing Iris mode *)
  End Lemma_Defs.
End Lemma_Spec.


