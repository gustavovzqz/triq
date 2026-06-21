From Triq Require StringLang.
From Stdlib Require Import Nat.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.


Theorem compute_program_add : forall 
  (p_str : StringLang.program) n n' snap, 
  StringLang.compute_program p_str snap (n + n') =
  StringLang.compute_program p_str (StringLang.compute_program p_str snap n') n.
Proof.
  intros p_str. induction n; intros n' snap.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.
