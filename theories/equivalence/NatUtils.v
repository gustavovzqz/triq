From Triq Require NatLang.
From Triq Require Import LanguagesCommon.

From Stdlib Require Import Nat.
From Stdlib Require Import List.
From Stdlib Require Extraction.
From Stdlib Require Import Lia.
Import ListNotations.

(** ** Obtendo a Maior Variável Z em p_nat *)

Fixpoint max_z_nat (l : NatLang.program) : nat :=
    match l with
    | [] => 0
    | NatLang.Instr opt_lbl (NatLang.INCR (Z n))  :: t 
    | NatLang.Instr opt_lbl (NatLang.DECR (Z n))  :: t 
    | NatLang.Instr opt_lbl (NatLang.IF_GOTO (Z n) _ )  :: t  =>
      Nat.max n (max_z_nat t) 
    | _ :: t => max_z_nat t
    end.

