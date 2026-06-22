From Triq Require StringLang.
From Triq Require NatLang.
From Triq Require Import LanguagesCommon.
From Triq Require StringUtils.

From Stdlib Require Import List.
Import ListNotations.


(* ------------------------------------------------------------------ *)
(* IF MACRO *)

(*
  Em Nat
  [instr_lbl] IF X != 0 GOTO l 

  Em String max_char
  [instr_lbl] IF X ends 0 GOTO l
  ...
  [instr_lbl] IF x ends max_char GOTO l
*)

Fixpoint get_if_macro 
  (x : variable)
  (instr_lbl : option label)
  (goto_lbl : option label)
  (max_char : nat) : StringLang.program :=

  match max_char with 
  | 0 => [StringLang.Instr instr_lbl (StringLang.IF_ENDS_GOTO x 0 goto_lbl)]
  | S n => (StringLang.Instr instr_lbl (StringLang.IF_ENDS_GOTO x max_char goto_lbl))
           :: get_if_macro x instr_lbl goto_lbl n
  end.

Compute get_if_macro Y None None 10.



(* ------------------------------------------------------------------ *)

(* Str Macro and Programs *)

Definition get_str_macro 
  (i_nat : NatLang.instruction) 
  (max_char : nat) 
  (max_label_p_nat max_z_p_nat max_label_p_str : nat) 
  : (StringLang.program) := 
  match i_nat with 
  | NatLang.Instr o (NatLang.INCR x) => [] (* TODO *)
  | NatLang.Instr o (NatLang.DECR x) => [] (* TODO *)
  | NatLang.Instr o (NatLang.IF_GOTO x l) => get_if_macro x o l max_char
end.

(* Macro Length *)
Definition macro_length instr max_char :=
  length (get_str_macro instr max_char 0 0 0).


(* Getting the Str Program *)
Fixpoint get_str_prg_rec p_nat max_char max_label_p_nat max_z_p_nat :=
  match p_nat with
  | []     => []
  | h :: t => let str_rest := get_str_prg_rec t max_char 
              max_label_p_nat max_z_p_nat in 
              let max_label_rest := StringUtils.get_max_label_str str_rest in 
              (get_str_macro h max_char max_label_p_nat 
               max_z_p_nat max_label_rest)
               ++ str_rest
  end.



