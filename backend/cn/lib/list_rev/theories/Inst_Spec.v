(* Instantiation of the CN-exported specification
   using results from the prior theories. *)

Require Import ZArith Bool Lia.
Require Import CN_Lemmas.Gen_Spec.
Import CN_Lemmas.Gen_Spec.Types.
Require Import List.
Import ListNotations.

Module Inst.
(* nothing!! *)
End Inst.

Module Defs := CN_Lemmas.Gen_Spec.Defs (Inst).

Module Proofs.

(* now prove lemmas *)
Import Defs.
Open Scope Z.

Lemma Append_Nil_RList : Append_Nil_RList_type.
Proof.
  intros L1 _. 
  induction L1.
  + split; reflexivity.
  + simpl. destruct IHL1. split; auto. 
    rewrite H; auto.
Qed.

Lemma Append_Cons_RList : Append_Cons_RList_type.
Proof.
  intros L1 z L2 t.
  induction L1; auto.
  simpl. destruct IHL1. split; auto.
  rewrite H; auto.
Qed.


End Proofs.

Module InstOK: CN_Lemmas.Gen_Spec.Lemma_Spec(Inst).

  Module D := CN_Lemmas.Gen_Spec.Defs (Inst).

  Include Proofs.

End InstOK.
