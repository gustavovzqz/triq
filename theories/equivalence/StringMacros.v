From Triq Require StringLang.
From Triq Require NatLang.
From Triq Require Import LanguagesCommon.

From Stdlib Require Import List.
Import ListNotations.


(** IF Macro *)

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



Definition get_str_macro 
  (i_nat : NatLang.instruction) 
  (max_char : nat) 
  (max_label_p_nat max_z_p_nat max_label_p_str : nat) 
  : (StringLang.program) := 
  match i_nat with 
  | NatLang.Instr opt_lbl (NatLang.INCR x) => []
  | NatLang.Instr opt_lbl (NatLang.DECR x) => []
  | NatLang.Instr opt_lbl (NatLang.IF_GOTO x l) => []
end.

(*
Fixpoint get_str_prg_rec l n' n k max_char :=
match l with
| [] => []
| i_nat :: t => let (macro, max_n) := get_str_macro i_nat n n' k  in 
                  macro ++ (get_str_prg_rec t (n' + max_n) n k)
end.
*)

Fixpoint get_str_prg_rec p_nat 
  match p_nat with
  | []     => []
  | h :: t => let str_rest := get_str_prg_rec t in 
              let max_label_rest := max_label_str str_rest in 
              str_rest ++ [get_str_macro h max_label_p_nat max_z_p_nat max_str_rest]
  end.

(* Exemplo *)

(* X <- X + 1  
   X <- X - 1
   IF X != 0 GOTO L 
*)


(* 
Lemma labels_equiv_position_in :
forall p_nat label a b c,
  label_in_instr p_nat label = true ->
  equiv_pos
    p_nat
    (NatLang.get_labeled_instr p_nat (Some label))
    (get_str_prg_rec p_nat
    (get_labeled_instr (get_str_prg_rec p_nat a b c) (Some label)).
Proof.
*)

(* EM ALTO NÍVEL
   ENUNCIADO. Dado o programa P_NAT nos naturais e o programa P_STR em strings,
   Se a primeira aparição de uma label ocorre em p_nat na posição i, 
   então ela ocorre em p_str na posição equivalente i'

   Indução em p_nat
    Caso base ok

    Passo:
      p_nat := h :: t 
      p_str := [max_label_str (get_str_prg_rec t)] ++ get_str_macro h (...)
      
      H (label_in_instr t = true -> label_
      nth_error 
*)


