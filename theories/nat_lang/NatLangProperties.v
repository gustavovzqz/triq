From Triq Require NatLang.
From Coq Require Import List.
Import ListNotations.


Theorem compute_program_empty : forall n snap,
  NatLang.compute_program [] snap n = snap.
Proof.
  induction n; intros.
  + reflexivity.
  + unfold NatLang.compute_program. assert (NatLang.next_step [] snap = snap).
    { unfold NatLang.next_step. destruct snap. rewrite nth_error_nil. reflexivity. }
    rewrite H. simpl. fold NatLang.compute_program. apply IHn.
Qed.




