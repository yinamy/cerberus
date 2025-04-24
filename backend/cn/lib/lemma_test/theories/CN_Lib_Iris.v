Require Import ZArith Bool Lia.
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export gen_heap.

(* Instantiating Iris with a heap *)

Notation Ptr := Z.
Notation Val := (option Z).


Class heapGS_gen Σ := HeapGS {
  heapGS_gen_heapGS :: gen_heapGS Ptr Val Σ;
}.

Notation heapGS := (heapGS_gen).

Notation "l ↦ v" := (pointsto l (DfracOwn 1) v) (at level 20) : bi_scope.

Section CN_Lib_Iris.

Context `{!heapGS Σ}.

(* Own and its various flavours *)

Definition Owned (l: Ptr) (v : Z) : iProp Σ := (l ↦ Some v)%I.
Definition Block (l :Ptr) : iProp Σ := (l ↦ None)%I. 

(* todo : is char supposed to be Z?*)
Definition Owned_char (l: Ptr) (v : Z) : iProp Σ := Owned l v.


Definition Owned_test (l: Ptr) (v : Z) : iProp Σ := Owned l v
∗ Owned l v.

(* todo: int should not occupy the same amount of heap memory as char*)
Definition Owned_int (l: Ptr) (v : Z) : iProp Σ := Owned l v.

(* todo: size *)
Definition shift (l: Ptr) (offset : Z) := 
  Z.add offset l.

(* padding *)

Definition arrayshift (l: Ptr) (pos : Z) (size : Z) := Z.add (Z.mul pos size) l.

Fixpoint padding (l : Ptr) (n : nat) := 
  match n with
  | 0 => (l ↦ None)%I
  | S n' => (Block l ∗ padding (l + 1) n')%I
  end.
  
End CN_Lib_Iris.