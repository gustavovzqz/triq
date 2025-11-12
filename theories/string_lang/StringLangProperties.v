From Triq Require StringLang.
From Coq Require Import Nat.
From Coq Require Import List.
From Coq Require Import Lia.
Import ListNotations.


Theorem compute_program_add : forall 
  {k} (p_str : StringLang.program k) n n' snap, 
  StringLang.compute_program p_str snap (n + n') =
  StringLang.compute_program p_str (StringLang.compute_program p_str snap n') n.
Proof.
  intros k p_str. induction n; intros n' snap.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.
