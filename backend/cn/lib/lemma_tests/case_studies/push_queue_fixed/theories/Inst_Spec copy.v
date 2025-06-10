(* Instantiation of the CN-exported specification
   using results from the prior theories. *)

Require Import ZArith Bool Lia.
Require Import CN_Lemmas.Gen_Spec.
Require Import CN_Lemmas.CN_Lib_Iris.
Import CN_Lemmas.Gen_Spec.Types.
From iris.proofmode Require Import proofmode.
Require Import iris.base_logic.lib.gen_heap.
Require Import Coq.Classes.RelationClasses.



Module Inst.

  Definition Alloc : (Z * Z) -> Prop := fun x => True.
  
End Inst.

Module Lemma_Defs := CN_Lemmas.Gen_Spec.Lemma_Defs (Inst).

Module Proofs.

(* now prove lemmas *)
Import Lemma_Defs Inst.
Open Scope Z.

Module Defs := CN_Lemmas.Gen_Spec.Defs (Inst).
Import Defs.

Section Iris_time.
Context `{!heapGS_gen Σ}.
Local Notation "⊢ P" := (⊢@{iPropI Σ} P).


Lemma queue_aux_nil : ⊢ ∀ (f : Ptr) (L : List),
  D.QueueAux f f L -∗ ⌜ L = Nil⌝ .
Proof.
  iIntros (f L) "H".
  destruct L. 
  - iPureIntro; auto.
  - unfold D.QueueAux.
    iDestruct "H" as "[H1 | H2]".
    + iDestruct "H1" as %H1.
      iPureIntro.
      exfalso.
      destruct H1; discriminate.
    + iExFalso.
      iDestruct "H2" as "[_ [ H _ ]]".
      iDestruct "H" as %H; easy.
Admitted.

Lemma queue_aux_nil_2 : ⊢ ∀ (f f' : Ptr) (L : List),
D.QueueAux f f' L -∗ ⌜ L = Nil -> f = f'⌝ .
Proof.
  iIntros (f f' L) "H".
  destruct L.
  - unfold D.QueueAux.
    iDestruct "H" as "[H1 | H2]".
    + iDestruct "H1" as %H1.
      iPureIntro.
      destruct H1; auto.
    + iExFalso.
      iDestruct "H2" as "[_ [ _ [%x [ _ [_ [_ [%y [_ HP]]]]]]]]".
      iDestruct "HP" as %H2.
      discriminate.
  - iPureIntro.
    intros P.
    discriminate.
Admitted.

Lemma queue_aux_false : ⊢ ∀ (f f' : Ptr) (L : List),
D.QueueAux f f' L -∗ ⌜ L = Nil -> (f ≠ f' -> False) ⌝.
  iIntros (f f' L) "H".
  induction L.
  - iEval (iApply queue_aux_nil_2) in "H".
    iDestruct "H" as %H.
    iPureIntro.
    destruct H; auto.
  - iPureIntro.
    intros H2.
    discriminate.
Qed.

(*Lemma queue_aux_unique : ⊢ ∀ (f f': Ptr) (L L' : List),
  D.QueueAux f f' L -∗ D.QueueAux f f' L' -∗ ⌜ L = L'⌝ .
Proof.
  iIntros (f f' L L') "H1 H2".
  induction L.
  - induction L'.
    + iPureIntro; auto.
    + iEval (iApply queue_aux_nil_2) in "H1".
      iDestruct "H1" as %H1.
      rewrite H1; auto.
      iExFalso.
      iEval (iApply queue_aux_nil) in "H2".
      iDestruct "H2" as %H2.
      discriminate.
  - induction L'.
    + iEval (iApply queue_aux_nil_2) in "H2".
      iDestruct "H2" as %H2.
      rewrite H2; auto.
      iExFalso.
      iEval (iApply queue_aux_nil) in "H1".
      iDestruct "H1" as %H1.
      discriminate.
    + admit.
Admitted.*)

(*Lemma queue_aux_neq : ⊢ ∀ (f f' f'' : Ptr) (L : List) (C : D.queue_cell),
⌜ f ≠ f'⌝ -∗ D.QueueAux f f' L -∗ D.Owned_queue_cell f'' C -∗ ⌜ f ≠ f''⌝ .
Proof.
  iIntros (f f' f'' L C) "H1 H2 H3".
  unfold D.QueueAux.
  generalize dependent f'.
  induction L.
  - iIntros (f').
     iDestruct "H2" as "[H2 | H2]".
    + iDestruct "H2" as %[H1 H2].
      iDestruct "H1" as %H3.
      contradiction.
    + iDestruct "H2" as "[_ [ _ [%x [ _ [_ [_ [%y [_ HP]]]]]]]]".
      iDestruct "HP" as %H4.
      discriminate.
  - iIntros (f').
  iDestruct "H2" as "[H2 | H2]".
    + iDestruct "H2" as %[H1 H2].
      iDestruct "H1" as %H3.
      contradiction.
    + admit. 
  Admitted.*)


Lemma owned_queue_cell_unique : ⊢ ∀ (f f' : Ptr) (C C' : D.queue_cell),
  D.Owned_queue_cell f C -∗ D.Owned_queue_cell f' C' -∗ ⌜ f ≠ f'⌝ .
Proof.
  unfold D.Owned_queue_cell.
  iIntros (f f' C C') "[H1 _] [H2 _]".
  unfold Owned_int.
  destruct (int_to_bytes (D.first C)).
  destruct p; destruct p.
  destruct (int_to_bytes (D.first C')).
  destruct p; destruct p.
  iDestruct "H1" as "[H1 _]".
  iDestruct "H2" as "[H2 _]".
  iApply (pointsto_ne with "H1 H2").
Qed.

Lemma front_last_neq : ⊢ ∀ (f f' f'' : Ptr) (c : D.queue_cell) (H : f ≠ f') (L : List) ,
  D.QueueAux f f' L -∗ D.Owned_queue_cell f'' c
-∗ ⌜ f ≠ f''⌝ .
(*Lemma front_last_neq (f f' f'' : Ptr) (c : D.queue_cell) (L : List) (H : f ≠ f') : ⊢
  D.QueueAux f f' L -∗ D.Owned_queue_cell f'' c
-∗ ⌜ f ≠ f''⌝ .*)
(*Lemma front_last_neq : ⊢ ∀ (f f' f'' : Ptr) (c : D.queue_cell) (L : List),
  D.QueueAux f f' L -∗ D.Owned_queue_cell f'' c
  -∗ ⌜ f ≠ f'⌝ -∗ ⌜ f ≠ f''⌝ .*)
Proof.
  iIntros (f f' f'' c H L) "H1 H2".
  unfold D.QueueAux.
  induction L.
  - iDestruct "H1" as "[H1 | H1]".
    + iDestruct "H1" as %H1.
      destruct H1.
      contradiction.
    + iDestruct "H1" as "[_  [_ [%x [_ [_ [_ [%y [_ H6]]]]]]]]".
      iDestruct "H6" as %H6.
      discriminate.
  - iDestruct "H1" as "[H1 | H1]".
    + iDestruct "H1" as %H1.
      destruct H1.
      contradiction.
    + iDestruct "H1" as "[_ [_ H8]]".
      iDestruct "H8" as "[%x [H8 [H9 [H10 [%y [H11 %pat]]]]]]".
      iApply (owned_queue_cell_unique $! f f'' x c with "H8 H2").
Admitted.

Lemma cons_snoc (x y : Z) (L : List) : Cons x (Snoc L y) = Snoc (Cons x L) y.
Proof.
  induction L.
  - reflexivity.
  - simpl.
    destruct IHL.
    reflexivity.
Qed.


Lemma QueueAux_Snoc (front second_last last : Ptr) (Second_last Last : D.queue_cell)(Q : List) (H : D.next Second_last = last) (H2: second_last ≠ last) (H3: front ≠ last)(H4: front ≠ second_last):
   ⊢ D.QueueAux front second_last Q -∗ D.Owned_queue_cell second_last Second_last -∗
   D.Owned_queue_cell last Last -∗
    D.QueueAux front last (D.Snoc Q (D.first Second_last)) ∗
   ∃ Last2 : D.queue_cell,
     D.Owned_queue_cell last Last2
     ∧ ⌜D.Snoc Q (D.first Second_last) =
        D.Snoc Q (D.first Second_last)⌝ ∧ ⌜Last = Last2⌝ ∧ emp.
Proof.
  iIntros "H1 H2 H3".
  iInduction Q as [A | B] "IH" forall (front H3 H4).
  - iEval (iApply queue_aux_false) in "H1".
    iDestruct "H1" as %H1.
    destruct H1; auto.
  - cbn.
    iDestruct "H1" as "[H1 | H1]".
    + iDestruct "H1" as %H1.
      destruct H1; contradiction.
    + iDestruct "H1" as "[_ [_ H8]]".
      iDestruct "H8" as "[%x [H8 [H9 [H10 [%y [H11 %pat]]]]]]".
      inversion pat.
      iAssert (⌜D.next x ≠ last⌝)%I as %S.
      { iDestruct "H10" as "[%H10 | %H10]".
        - inversion H10; auto.
          iPureIntro; lia.
        - admit. } 
      (* TODO*)

      iSplitR "H3".
      iRight.
      iSplitR. auto.
      iSplitR. auto.
      iExists x.
      iSplitL "H8"; auto.
      iSplitL "H9"; auto.
      iSplitR.
      ++ iPureIntro; lia.
      ++ iExists (D.Snoc y (D.first Second_last)).
          iSplitL; auto.
          +++ assert (D.next x = last \/ D.next x ≠ last).
              lia.
              iDestruct "H10" as "[%H10 | %H10]".
              * inversion H10; auto. admit.
              * destruct H0. inversion H0.
                ** contradiction.
                ** 
                
                iAssert (∀ front0 : Ptr,
                ⌜front0 ≠ last⌝ -∗
                ⌜front0 ≠ second_last⌝ -∗
                D.QueueAux front0 second_last y -∗
                D.Owned_queue_cell second_last Second_last -∗
                D.Owned_queue_cell last Last -∗
                D.QueueAux front0 last
                  (D.Snoc y (D.first Second_last)))%I as "IH2".
                  iIntros (front1) "Z1 Z2 Z3 Z4 Z5".
                   iSpecialize ("IH" $! front1 with "Z1 Z2 Z3 Z4 Z5").
                  iDestruct "IH" as "[V B]".
                  iApply "V".
                  (* D.QueueAux front last (D.Snoc (Cons B Q) (D.first Second_last))*)
                  iApply "IH2".
                  now iPureIntro.
                  auto.
                  admit.
                  admit.
                  admit.
      ++ iExists (Last); auto.
Admitted.


Lemma push_induction : ⊢ push_induction_type.
  unfold push_induction_type.
  iIntros (front second_last last [H1 | H2] Q).
  - iIntros "H3" (Second_last) "H4 H5".
    iIntros (Last) "H6".
    iDestruct "H5" as %H5.
    iSplitR.
    + iPureIntro.
      lia.
    + rewrite H1.
      iExists (D.Snoc Q (D.first Second_last)).
      iEval (iApply queue_aux_nil) in "H3".
      iDestruct "H3" as %H3.
      iAssert (⌜second_last ≠ last⌝)%I as %P.
      iPoseProof (owned_queue_cell_unique $! second_last last Second_last Last with "H4 H6") as "H3"; auto.
      rewrite H3.
      iSplitR "H6"; auto.
      unfold D.Snoc.
      unfold D.QueueAux.
      iRight.
      iSplitR; iSimpl; auto.
      iSplitR.
      * iPureIntro.
        auto.
      * iExists Second_last.
        iSplitL "H4"; auto.
        iSplitR; auto.
        -- admit.
        -- iSplitR.
          ++ iPureIntro.
             lia.
          ++ iExists Nil.
            iSplitL; auto.
  - iIntros "H3" (Second_last) "H4 H5".
    iIntros (Last) "H6".
    iDestruct "H5" as %H5.
    iSplitR.
    + iPureIntro.
      lia.
    + iExists (D.Snoc Q (D.first Second_last)).
      iAssert (⌜second_last ≠ last⌝)%I as %P.
      iPoseProof (owned_queue_cell_unique $! second_last last Second_last Last with "H4 H6") as "H7"; auto.
      iAssert (⌜front ≠ last⌝)%I as %R.
      iPoseProof (front_last_neq $! front second_last last Last H2 with "H3 H6") as "%H7"; auto.
      iApply (QueueAux_Snoc with "H3 H4 H6"); auto.
        

      (*iEval (iApply queue_aux_nil) in "H3".
      * admit.
      (*iEval (iApply queue_aux_nil) in "H3".
        admit.
      * iExists (Last).
        iSplitL "H6"; auto.

      (*iEval (iApply queue_aux_nil) in "H3".
      *iExists Last.
       iSplitL "H6"; auto.


      (* iAssert (⌜second_last ≠ last⌝)%I as %P.
      iPoseProof (owned_queue_cell_unique $! second_last last Second_last Last with "H4 H6") as "H7"; auto.
      iAssert (⌜front ≠ last⌝)%I as %R.
      iApply (front_last_neq $! front second_last last Second_last Last Q with "H3 H6"); auto.
      (*iSplitR "H6"; auto.*)
      (*generalize dependent front.
            induction Q ; intros front wtv wtv2.
      *)
      iInduction Q as [A | B] "IH" forall (front last Last H2 H5 P R  ).
      * unfold D.Snoc.
        unfold D.QueueAux.
        iSplitR "H6"; auto.
        iRight.
        iSplitR; iSimpl; auto.
        iDestruct "H3" as "[H3 | H3]".
        -- iDestruct "H3" as "[%H3 _]".
           contradict H3; auto. 
        -- iDestruct "H3" as "[_  [_ [%x [_ [_ [_ [%y [_ H6]]]]]]]]".
          iDestruct "H6" as %H6.
          exfalso.
          discriminate.
      * cbn.
        iDestruct "H3" as "[H3 | H3]".
        -- iDestruct "H3" as "[%H3 _]".
          contradict H3; auto.
        -- iDestruct "H3" as "[_ [_ H8]]".
           iDestruct "H8" as "[%x [H8 [H9 [H10 [%y [H11 %pat]]]]]]".
           iAssert (⌜D.next x ≠ last⌝)%I as %S.
           admit.
           iSplitR "H6"; auto.
          iRight.
          iSplitR; auto.
          
          iSplitR.
          ** iPureIntro; auto.
          ** inversion pat.
            iExists x.
            iSplitL "H8"; auto.
            iSplitL "H9"; auto.
            iSplitR.
           ++ iPureIntro.
              lia.
           ++ iExists (D.Snoc y (D.first Second_last)).
              iSplitL; auto.
              rewrite <- H1.
              iDestruct "H10" as "[%H10 | %H10]".
              --- rewrite H10.
              iEval (iApply queue_aux_nil) in "H11".
              iDestruct "H11" as %H11.
              rewrite H11.
              unfold D.Snoc.
              unfold D.QueueAux.
              iRight.
              iSplitR; iSimpl; auto.
              iSplitR.
              *** iPureIntro; auto.
              *** iExists Second_last.
                  iSplitL "H4"; auto.
                  iSplitR; auto.
                  ---- admit.
                  ---- iSplitR.
                     **** iPureIntro.
                        lia.
                     **** iExists Nil.
                        iSplitL; auto.
              --- iRename "H11" into "H3".
                  iSpecialize ("IH" $! (D.next x) last Second_last H10 H5 P S).
                  iAssert 
                  (D.QueueAux (D.next x) second_last Q -∗
                  D.Owned_queue_cell second_last Second_last -∗ D.QueueAux (D.next x) last (D.Snoc Q (D.first Second_last)))%I with "[IH]" as "IHL".
                  ---- iIntros "A B".
                       iSpecialize ("IH" with "A B").

                  iDestruct "IH" as "A".
                  ---- iApply ("IHL" with "H3 H4"). *)
Admitted.
          
(*TODO*)
End Iris_time.
End Proofs.

Module InstOK: CN_Lemmas.Gen_Spec.Lemma_Spec(Inst).

  Module L := CN_Lemmas.Gen_Spec.Lemma_Defs (Inst).

  Include Proofs.

End InstOK.

