From Triq Require StringLang.
From Coq Require Import Nat.
From Coq Require Import List.
From Coq Require Import Lia.
Import ListNotations.




Theorem compute_program_empty :
  forall {k : nat} n (snap : StringLang.snapshot k),
  StringLang.compute_program [] snap n = snap.
Proof.
  induction n; intros.
  + reflexivity.
  + unfold StringLang.compute_program. assert (StringLang.next_step [] snap = snap).
    { unfold StringLang.next_step. destruct snap. rewrite nth_error_nil. reflexivity. }
    rewrite H. apply IHn.
Qed.


Theorem compute_program_append :
  forall {k : nat} n n' (p : StringLang.program k) (p' : StringLang.program k) snap,
  StringLang.compute_program (p ++ p') snap  (n' + n) =
  StringLang.compute_program p (StringLang.compute_program p' snap n') n.
Proof.
  induction n'; intros.
  + simpl. admit.
  + simpl.
  
  

