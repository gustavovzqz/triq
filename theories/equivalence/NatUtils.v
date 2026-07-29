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


Fixpoint get_max_label (l : NatLang.program) : nat :=
  match l with
  | [] => 0
  | NatLang.Instr opt_lbl _ :: t =>
      match opt_lbl with
      | None => get_max_label t
      | Some (A n) => Nat.max n (get_max_label t)
      end
  end.


(** * Label Pertence a Alguma Instrução em p_nat *)

Fixpoint label_in_instr p_nat (lbl : label)  :=
  match p_nat with
  | [] => false
  | NatLang.Instr opt_lbl _ :: t => match opt_lbl with 
                                       | Some lbl' => if eqb_lbl lbl lbl'
                                                      then true
                                                      else label_in_instr t lbl
                                       | None => label_in_instr t lbl
                                       end
  end.
