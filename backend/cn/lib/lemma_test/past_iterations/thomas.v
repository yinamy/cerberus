(* help.v: generated lemma specifications from CN *)

Require Import ZArith Bool.
Require CN_Lemmas.CN_Lib.


Module Types.

  Inductive
    tree : Type :=
    | Empty_Tree : tree
    | Node : tree_list -> Z -> tree
    with
    tree_list : Type :=
    | Empty_List : tree_list
    | Cons_List : tree -> tree_list -> tree_list.

End Types.


Module Type Parameters.
  Import Types.

  Parameter nth_tree_list : tree_list -> Z -> tree.

  Parameter array_to_tree_list : ((Z -> tree)) -> Z -> tree_list.

  Parameter in_tree : tree -> (((Z -> Z)) * Z * Z) -> bool.

  Parameter tree_v : tree -> (((Z -> Z)) * Z * Z) -> Z.

End Parameters.


Module Defs (P : Parameters).

  Import Types P.
  Open Scope Z.

  Definition get_i_1_3 {T_0 T_1 T_2: Type} (t : (T_0 * T_1 * T_2)) :=
    (let '(x_t_0,x_t_1,x_t_2) := (t : (T_0 * T_1 * T_2)) in
x_t_1).

  Definition get_len_2_3 {T_0 T_1 T_2: Type} (t : (T_0 * T_1 * T_2)) :=
    (let '(x_t_0,x_t_1,x_t_2) := (t : (T_0 * T_1 * T_2)) in
x_t_2).

  Definition get_arr_0_3 {T_0 T_1 T_2: Type} (t : (T_0 * T_1 * T_2)) :=
    (let '(x_t_0,x_t_1,x_t_2) := (t : (T_0 * T_1 * T_2)) in
x_t_0).

  Definition in_tree_tree_v_lemma_type : Prop :=
    forall (t : tree),

forall (arc : (((Z -> Z)) * Z * Z)),

forall (t_children : ((Z -> tree))),

(0 <= (get_i_1_3 arc)) ->
((get_len_2_3 arc) <= 65536) ->
((tree_v t arc) =

(match t with | (Empty_Tree) => 0
| (Node children v) =>
(let arc2 := ((get_arr_0_3 arc), (CN_Lib.wrapI (-2147483648) 2147483647 ((get_i_1_3 arc) + 1)),
(get_len_2_3 arc)) in (if ((get_i_1_3 arc) <? (get_len_2_3 arc)) then
(tree_v (nth_tree_list children ((get_arr_0_3 arc) (get_i_1_3 arc))) arc2) else v)) end)) /\ ((in_tree t
arc) =
(match t with | (Empty_Tree) => false
| (Node children v) =>
(let arc2 := ((get_arr_0_3 arc), (CN_Lib.wrapI (-2147483648) 2147483647 ((get_i_1_3 arc) + 1)),
(get_len_2_3 arc)) in (if ((get_i_1_3 arc) <? (get_len_2_3 arc)) then
(in_tree (nth_tree_list children ((get_arr_0_3 arc) (get_i_1_3 arc))) arc2) else true)) end)) /\ let i := ((get_arr_0_3
arc) (get_i_1_3 arc)) in
(if ((0 <=? i) && (i <? 16)) 
then ((nth_tree_list (array_to_tree_list t_children 16) i) = (t_children i))
else (Is_true true)).

End Defs.


Module Type Lemma_Spec (P : Parameters).

  Module D := Defs(P).
  Import D.

  Parameter in_tree_tree_v_lemma : in_tree_tree_v_lemma_type.

End Lemma_Spec.


