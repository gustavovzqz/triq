
From Triq Require Import StringLang.

From Stdlib Require Import Nat.
From Stdlib Require Import List.

Import ListNotations.


Open Scope string_lang_scope.

Theorem t0_lt_1 : 0 < 1.
Proof.
  constructor.
Qed.


Definition prg :=
  <{[ Instr None (APPEND (exist _ 0 t0_lt_1) (X 0))]}>.

Check (prg : program 1).
