From Triq Require StringLang.
From Triq Require NatLang.

From Stdlib Require Import List.
Import ListNotations.

Definition get_str_macro 
  (i_nat : NatLang.instruction) 
  (max_char : nat) 
  (n n' k : nat) 
  : (StringLang.program) := 
match i_nat with 
| NatLang.Instr opt_lbl (NatLang.INCR x) => []
| NatLang.Instr opt_lbl (NatLang.DECR x) => []
| NatLang.Instr opt_lbl (NatLang.IF_GOTO x l) => []
end.
