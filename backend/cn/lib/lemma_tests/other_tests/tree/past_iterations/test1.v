(* test1.v: generated lemma specifications from CN *)

Require Import ZArith Bool.
Require CN_Lemmas.CN_Lib.


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


Module Defs (P : Parameters).

  Import Types P.
  Open Scope Z.


  Definition in_tree_tree_v_lemma_type : Prop :=
    forall (t : tree),
forall (arc : (((Z -> Z)) * Z * Z)),
forall (t_children : ((Z -> tree))),
((0) <= (get_i arc)) -> ((get_len arc) <= (65536)) -> ((tree_v t arc) = (tree_v_step t arc)) /\ ((in_tree t
arc) = (in_tree_step t arc)) /\ (let i := ((get_arr arc) (get_i arc)) in (if (((0) <=? i) && (i <? (16)))
then ((nth_tree_list (array_to_tree_list t_children (16)) i) = (t_children i)) else (Is_true true)) /\ Is_true true).

End Defs.


Module Type Lemma_Spec (P : Parameters).

  Module D := Defs(P).
  Import D.

  Parameter in_tree_tree_v_lemma : in_tree_tree_v_lemma_type.

End Lemma_Spec.


