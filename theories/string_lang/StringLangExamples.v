
From Triq Require Import StringLang.

From Coq Require Import Nat.
From Coq Require Import List.

Import ListNotations.


Open Scope string_lang_scope.

Theorem t0_le_1 : 0 <= 1.
Proof.
  constructor. constructor.
Qed.


Definition prg :=
  <{[ Instr None (APPEND (Char _ 0 t0_le_1) (X 0))]}>.

Check (prg : program 1).
