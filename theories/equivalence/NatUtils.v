From Triq Require NatLang.
From Triq Require Import LanguagesCommon.

From Stdlib Require Import Nat.
From Stdlib Require Import List.
From Stdlib Require Extraction.
From Stdlib Require Import Lia.
Import ListNotations.

(** ** Obtendo a Maior Variável Z em p_nat *)

Fixpoint get_max_z (l : NatLang.program) : nat :=
    match l with
    | [] => 0
    | NatLang.Instr opt_lbl (NatLang.INCR (Z n))  :: t 
    | NatLang.Instr opt_lbl (NatLang.DECR (Z n))  :: t 
    | NatLang.Instr opt_lbl (NatLang.IF_GOTO (Z n) _ )  :: t  =>
      Nat.max n (get_max_z t) 
    | _ :: t => get_max_z t
    end.


(** ** Obtendo a Maior Label em p_nat *)

Definition max_opts opt_lbl goto_lbl k :=
match opt_lbl, goto_lbl with
| Some (A n), Some (A n') => max (max n n') k 
| Some (A n), None => max n k
| None, Some (A n') => max n' k
| None, None => k
end.


Fixpoint get_max_label (l : NatLang.program) : nat :=
    match l with
    | [] => 0
    | NatLang.Instr opt_lbl (NatLang.IF_GOTO _ goto_lbl) :: t =>
      (max_opts opt_lbl goto_lbl (get_max_label t))
    | NatLang.Instr opt_lbl _ :: t =>
        match opt_lbl with
        | None => get_max_label t
        | Some (A n) => max (get_max_label t) n
        end
    end.

