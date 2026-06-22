From Triq Require NatLang.
From Triq Require StringLang.

From Triq Require NatLangProperties.
From Triq Require StringLangProperties.

From Triq Require Import LanguagesCommon.
From Triq Require StringMacros.

From Triq Require NatUtils.
From Triq Require StringUtils.
From Triq Require LanguagesUtils.

From Stdlib Require Import Nat.
From Stdlib Require Import List.
From Stdlib Require Import Lia.

Import ListNotations.

(** Equivalência entre estados *)

Definition state_equiv (s_nat : NatLang.state) (s_str : StringLang.state) 
  (max_char : nat) :=
  forall (x : variable),
  LanguagesUtils.nat_to_string (s_nat x) max_char = s_str x.


Definition get_equiv_simulated_position 
  (p_nat : NatLang.program) 
  (n : nat)
  (max_char : nat) :=
fold_left
  (fun acc instr => acc + StringMacros.macro_length instr max_char)
  (firstn n p_nat)
0.

Definition equiv_pos 
(p_nat : NatLang.program) (n : nat)
(p_str : StringLang.program ) (n' : nat) (max_char : nat) :=
n' = get_equiv_simulated_position p_nat n max_char.


(** Teorema Principal *)
Theorem nat_implies_string :
  forall (p_nat : NatLang.program)
         (initial_state_nat : NatLang.state)
         (max_char : nat),
  NatLangProperties.is_initial_state initial_state_nat ->

  exists (p_str : StringLang.program)
        (initial_state_str : StringLang.state),
  StringLang.program_over p_str max_char /\
  StringLang.state_over initial_state_str max_char /\

  forall (n : nat),
  exists (n' : nat),

  let (line_nat, state_nat) := NatLang.split_snap 
      (NatLang.compute_program p_nat (NatLang.SNAP 0 initial_state_nat) n)  in

  let (line_str , state_str) := StringLang.split_snap
            (StringLang.compute_program p_str (StringLang.SNAP 0 initial_state_str) n') in

  state_equiv state_nat state_str max_char /\
  equiv_pos p_nat line_nat p_str line_str max_char /\
  state_str (Z (NatUtils.max_z_nat p_nat + 1)) = [] /\
  state_str (Z (NatUtils.max_z_nat p_nat + 2)) = [] /\
  StringLang.state_over state_str max_char.

Proof.
Admitted. 
