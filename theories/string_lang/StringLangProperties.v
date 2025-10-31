From Triq Require StringLang.
From Coq Require Import Nat.
From Coq Require Import List.
Import ListNotations.



Lemma compute_program_empty :
  forall {k : nat} n (snap : StringLang.snapshot k),
  StringLang.compute_program [] snap n = snap.
Proof.
  induction n; intros.
  + reflexivity.
  + unfold StringLang.compute_program. assert (StringLang.next_step [] snap = snap).
    { unfold StringLang.next_step. destruct snap. rewrite nth_error_nil. reflexivity. }
    rewrite H. apply IHn.
Qed.



