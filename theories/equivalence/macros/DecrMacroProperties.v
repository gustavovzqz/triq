From Triq Require StringLang.
From Triq Require Import LanguagesCommon.
From Triq Require Import LanguagesUtils.
From Triq Require StringUtils.
From Triq Require Import StringMacros.
From Triq Require TransferMacroProperties.

From Triq Require Import MacroTactics.


From Stdlib Require Import List.
From Stdlib Require Import Lia.


From AAC_tactics Require Import AAC.
From AAC_tactics Require Instances.
Import Instances.Lists.
Import ListNotations.

(* Lema: executing with char greater than zero leades do t1 with char = char - 1*)

Lemma compute_char_decr_aux :
  forall max_char p_str pos_str state_str 
         label_idx x z if_goto_idx
         h t goto_label skip_block aux char s,

  p_str = h ++
  get_if_macro_label x (Some (A label_idx)) max_char if_goto_idx ++
  skip_block ++
  get_all_ai_blocks_decr x z aux max_char if_goto_idx goto_label ++ t ->

  StringUtils.labels_greater_than skip_block 
  (max_char + if_goto_idx) ->

  StringUtils.labels_less_than h if_goto_idx ->

  label_idx < if_goto_idx ->

  length h = pos_str  ->

  state_str x = char :: s ->

  char <= max_char ->
  char > 0 -> 
  StringLang.ends_with (state_str aux) 0 = true ->


  eqb_var x z = false ->
  eqb_var x aux = false ->
  eqb_var z aux = false ->


  exists n,
  let (line_str, state_str') :=
    StringLang.split_snap
      (StringLang.compute_program p_str (StringLang.SNAP pos_str state_str)
         n) in

  (line_str = StringLang.get_labeled_instr p_str goto_label /\
  state_str' x = s /\
  state_str' z =  (state_str z) ++ [char - 1]) /\
  forall var, 
  (var <> x /\ var <> z) ->
  state_str' var = state_str var.
Proof.
Admitted.


Lemma compute_char_decr :
  forall max_char p_str pos_str state_str 
          x z label_idx if_goto_idx h t aux char s T1 T2,


  p_str = h ++
  get_if_macro_label x (Some (A (label_idx))) max_char if_goto_idx ++ 
  [StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 T2)] ++

  get_all_ai_blocks_decr x z aux max_char if_goto_idx T1 ++

  [StringLang.Instr (Some (A (if_goto_idx))) (StringLang.DEL x)] ++
  get_if_macro x None (A (if_goto_idx + max_char + 1)) max_char ++
  [StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 T2)] ++


  [StringLang.Instr (Some (A (if_goto_idx + max_char + 1))) (StringLang.APPEND max_char z)] ++
  [StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 (A (label_idx)))] ++
  t ->

  StringUtils.labels_less_than h if_goto_idx ->


  length h = pos_str  ->

  state_str x = char :: s ->

  label_idx < if_goto_idx ->

  char <= max_char ->

  StringLang.ends_with (state_str aux) 0 = true ->


  eqb_var x z = false ->
  eqb_var x aux = false ->
  eqb_var z aux = false ->


  exists n,

  let (line_str, state_str') :=
    StringLang.split_snap (StringLang.compute_program p_str
    (StringLang.SNAP pos_str state_str) n) in

  (* Caso 1: 0 :: [] *)
  (char = 0 /\ s = [] ->
    line_str = StringLang.get_labeled_instr p_str T2 /\
    state_str' x = [] /\
    state_str' z = state_str z)
  /\
  (* Caso 2: 0 :: s *)
  (char = 0 /\ s <> [] ->
    line_str = StringLang.get_labeled_instr p_str T1 /\
    state_str' x = s /\
    state_str' z = state_str z)
  /\

  (* Caso 3: char :: l *)
  (char > 0 ->
    line_str = StringLang.get_labeled_instr p_str T1 /\
    state_str' x = s /\
    state_str' z = (state_str z) ++ [char - 1])
  /\
  forall var, (var <> x /\ var <> z) ->
    state_str' var = state_str var.
Proof.
Admitted.

Lemma compute_decr_macro_aux :
  forall max_char p_str pos_str state_str 
         instr_label x 
         max_label_nat max_z_nat  h t x_value, 

  let max_label_str := StringUtils.get_max_label h in 

  p_str = h ++
  StringMacros.get_str_macro 
  (NatLang.Instr instr_label (NatLang.DECR x)) 
  max_char max_label_nat max_z_nat
  max_label_str ++ t  ->

  length h = pos_str  ->

  label_le_idx instr_label max_label_nat ->

  StringLang.state_over state_str max_char ->

  StringLang.string_over x_value max_char -> 


  state_str x = x_value ->
  state_str (Z (max_z_nat + 2)) = [0] ->

  eqb_var x (Z (max_z_nat + 2)) = false ->
  eqb_var x (Z (max_z_nat + 1)) = false ->

  exists n,
  let (line_str, state_str') :=
    StringLang.split_snap
      (StringLang.compute_program p_str (StringLang.SNAP (pos_str + 1) state_str)
         n) in

  line_str = StringLang.get_labeled_instr p_str (A 
  (max_label_nat + max_label_str + max_char + max_char + 6)) /\  
  state_str' x = []  /\
  state_str' (Z (max_z_nat + 1)) = state_str (Z (max_z_nat + 1)) 
             ++ decr_string (state_str x) max_char /\
  forall var, 
  var <> x /\ var <> (Z (max_z_nat + 1)) ->
  state_str' var = state_str var.
Proof.
Admitted.


Lemma compute_decr_macro :
  forall max_char p_str pos_str state_str 
         instr_label x 
         max_label_nat max_z_nat  h t x_value, 

  let max_label_str := StringUtils.get_max_label h in 

  p_str = h ++
  StringMacros.get_str_macro 
  (NatLang.Instr instr_label (NatLang.DECR x)) 
  max_char max_label_nat max_z_nat
  max_label_str ++ t  ->

  length h = pos_str  ->

  label_le_idx instr_label max_label_nat ->

  StringLang.state_over state_str max_char ->

  StringLang.string_over x_value max_char -> 


  state_str x = x_value ->
  state_str (Z (max_z_nat + 2)) = [] ->

  eqb_var x (Z (max_z_nat + 2)) = false ->
  eqb_var x (Z (max_z_nat + 1)) = false ->

  exists n,
  let (line_str, state_str') :=
    StringLang.split_snap
      (StringLang.compute_program p_str (StringLang.SNAP pos_str state_str)
         n) in

  line_str = pos_str + StringMacros.macro_length 
  (NatLang.Instr instr_label (NatLang.DECR x)) max_char /\  
  state_str' x = state_str (Z (max_z_nat + 1)) 
             ++ decr_string (state_str x) max_char  /\
  state_str' (Z (max_z_nat + 1)) = [] /\
  forall var, 
  var <> x /\ var <> (Z (max_z_nat + 1)) ->
  state_str' var = state_str var.
Proof.
Admitted.