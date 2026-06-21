
From Triq Require Import StringLang.

From Stdlib Require Import Nat.
From Stdlib Require Import List.

Import ListNotations.


Open Scope string_lang_scope.

Theorem t0_le_1 : 0 <= 1.
Proof.
  constructor. constructor.
Qed.


Definition prg :=
  <{[ Instr None (APPEND 0 (X 0))]}>.

Check (prg : program).

Lemma prg_string_1 : program_over prg 1.
Proof.
  split; simpl; auto.
Qed. 



