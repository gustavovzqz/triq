From Triq Require StringLang.
From Triq Require Import LanguagesCommon.

From Stdlib Require Import Nat.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.


Fixpoint get_max_label_str (l : StringLang.program) : nat :=
  match l with
  | [] => 0
  | StringLang.Instr opt_lbl _ :: t =>
      match opt_lbl with
      | None => get_max_label_str t
      | Some (A n) => Nat.max n (get_max_label_str t)
      end
  end.
