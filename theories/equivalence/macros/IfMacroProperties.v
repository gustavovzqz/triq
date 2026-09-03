From Triq Require StringLang.
From Triq Require Import LanguagesCommon.

From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.


From Triq Require Import StringMacros.

Lemma compute_if_block_skip :
  forall max_char p_str pos_str state_str 
         instr_label x goto_label
         max_label_nat max_z_nat max_z_str h t, 

  p_str = h ++
  StringMacros.get_str_macro 
  (NatLang.Instr instr_label (NatLang.IF_GOTO x goto_label)) 
  max_char max_label_nat max_z_nat
  max_z_str ++ t  ->

  length h = pos_str  ->


  state_str x = [] ->

  exists n,
  let (line_str, state_str') :=
    StringLang.split_snap
      (StringLang.compute_program p_str (StringLang.SNAP pos_str state_str)
         n) in

  state_str' = state_str /\
  line_str = pos_str + StringMacros.macro_length 
  (NatLang.Instr instr_label (NatLang.IF_GOTO x goto_label)) 
  max_char.
Proof.
  Transparent StringMacros.get_str_macro.
  induction max_char;
  intros p_str pos_str state_str instr_label
  x goto_label max_label_nat max_z_nat max_z_str h t;
  intros p_str_decomposition H_length H_state_str.
  - rewrite p_str_decomposition. 
    exists 1. simpl. rewrite nth_error_app2 by lia.
    rewrite H_length, PeanoNat.Nat.sub_diag.
    simpl.
    rewrite H_state_str. simpl. unfold StringMacros.macro_length.
    repeat (split; auto).
    (* Passo *)
  - cut (exists n n' : nat, 
    let (line_str, state_str') := StringLang.split_snap
    (StringLang.compute_program p_str (StringLang.compute_program p_str 
    (StringLang.SNAP pos_str state_str) n) n') 
    in state_str' = state_str /\ line_str = pos_str + 
    StringMacros.macro_length 
    (NatLang.Instr instr_label (NatLang.IF_GOTO x goto_label)) (S max_char)).
    {intros cH. destruct cH as [m [m']]. exists (m' + m). 
     rewrite StringLangProperties.compute_program_add. auto. }
    exists 1. simpl. rewrite p_str_decomposition, nth_error_app2 by lia.
    rewrite <- p_str_decomposition.
    rewrite H_length, PeanoNat.Nat.sub_diag. simpl.
    rewrite H_state_str. simpl.
    simpl in p_str_decomposition.
    unfold StringMacros.macro_length in *. simpl. 
    remember  (length (StringMacros.get_if_macro x instr_label 
    goto_label max_char)) as if_length.
    replace (pos_str + S if_length) with (pos_str + 1 + if_length) by lia.
    rewrite Heqif_length. 
    rewrite LanguagesUtils.cons_app_assoc in p_str_decomposition.
    rewrite app_assoc in p_str_decomposition.
    remember  (h ++ [StringLang.Instr instr_label
    (StringLang.IF_ENDS_GOTO x (S max_char) goto_label)]) as h'.
    apply IHmax_char with (max_label_nat := max_label_nat)
    (max_z_nat := max_z_nat) (max_z_str := max_z_str)
    (h := h') (t := t); auto.
    rewrite Heqh', length_app, H_length. 
    reflexivity.
Qed.


Lemma compute_if_block_Sn :
  forall max_char p_str pos_str state_str 
         instr_label x goto_label
         max_label_nat max_z_nat max_z_str h t char,

  p_str = h ++
  get_str_macro 
  (NatLang.Instr instr_label (NatLang.IF_GOTO x goto_label)) 
  max_char max_label_nat max_z_nat
  max_z_str ++ t  ->

  length h = pos_str  ->

  char <= max_char ->

  StringLang.ends_with (state_str x) char = true ->

  exists n,
  let (line_str, state_str') :=
    StringLang.split_snap
      (StringLang.compute_program p_str (StringLang.SNAP pos_str state_str)
         n) in

  state_str' = state_str /\
  line_str = StringLang.get_labeled_instr p_str goto_label.
Proof.
  Transparent get_str_macro.
  induction max_char;
  intros p_str pos_str state_str instr_label
  x goto_label max_label_nat max_z_nat max_z_str h t char;
  intros p_str_decomposition H_length char_H H_state_str.
  - rewrite p_str_decomposition. 
    exists 1. simpl. rewrite nth_error_app2 by lia.
    rewrite H_length, PeanoNat.Nat.sub_diag.
    simpl. assert (char = 0) as char_0 by lia. rewrite char_0 in *.
    rewrite H_state_str. simpl. unfold macro_length.
    repeat (split; auto).
    (* Passo *)
  - cut (exists n n' : nat, 
    let (line_str, state_str') := StringLang.split_snap
    (StringLang.compute_program p_str (StringLang.compute_program p_str 
    (StringLang.SNAP pos_str state_str) n) n') 
    in state_str' = state_str /\ 
    line_str = StringLang.get_labeled_instr p_str goto_label).
    {intros cH. destruct cH as [m [m']]. exists (m' + m). 
     rewrite StringLangProperties.compute_program_add. auto. }
    exists 1. simpl. rewrite p_str_decomposition, nth_error_app2 by lia.
    rewrite <- p_str_decomposition.
    rewrite H_length, PeanoNat.Nat.sub_diag. simpl.
    assert (char = S max_char \/ char <> S max_char) as char_cases by lia.
    destruct char_cases as [char_eq_S | char_diff_S].
    + rewrite char_eq_S in *. rewrite H_state_str. simpl.
      simpl in p_str_decomposition.
      unfold macro_length in *. simpl.  exists 0.
      simpl. repeat split; auto.
    + assert (StringLang.ends_with (state_str x) (S max_char) = false) 
      as ends_with_S_false.
      { destruct (state_str x); auto. simpl in H_state_str. simpl. 
        rewrite PeanoNat.Nat.eqb_neq.
        rewrite PeanoNat.Nat.eqb_eq in H_state_str. lia. }
      assert (char <= max_char) as char_leq_max_char by lia.
      rewrite ends_with_S_false. simpl in p_str_decomposition.
      rewrite LanguagesUtils.cons_app_assoc in p_str_decomposition.
      rewrite app_assoc in p_str_decomposition.
      remember  (h ++ [StringLang.Instr instr_label
      (StringLang.IF_ENDS_GOTO x (S max_char) goto_label)]) as h'.
      apply IHmax_char with (max_label_nat := max_label_nat)
      (max_z_nat := max_z_nat) (max_z_str := max_z_str) 
      (instr_label := instr_label) (x := x) (char := char)
      (h := h') (t := t); auto.
      rewrite Heqh', length_app, H_length. reflexivity.
Qed.

Lemma compute_if_block_label_skip :
  forall max_char p_str pos_str state_str 
         x opt_label if_goto_idx h t, 

  p_str = h ++
  get_if_macro_label x opt_label max_char if_goto_idx
  ++ t  ->

  length h = pos_str  ->


  state_str x = [] ->

  exists n,
  let (line_str, state_str') :=
    StringLang.split_snap
      (StringLang.compute_program p_str (StringLang.SNAP pos_str state_str)
         n) in

  state_str' = state_str /\
  line_str = pos_str + length (get_if_macro_label x opt_label max_char if_goto_idx).
Proof.
  Transparent StringMacros.get_str_macro.
  induction max_char;
  intros p_str pos_str state_str x opt_label if_goto_idx h t;
  intros p_str_decomposition H_length H_state_str.
  - rewrite p_str_decomposition. 
    exists 1. simpl. rewrite nth_error_app2 by lia.
    rewrite H_length, PeanoNat.Nat.sub_diag.
    simpl.
    rewrite H_state_str. simpl. unfold StringMacros.macro_length.
    repeat (split; auto).
    (* Passo *)
  - cut (exists n n' : nat, 
    let (line_str, state_str') := StringLang.split_snap
    (StringLang.compute_program p_str (StringLang.compute_program p_str 
    (StringLang.SNAP pos_str state_str) n) n') 
    in state_str' = state_str /\ 
       line_str = pos_str + 
    length (get_if_macro_label x opt_label (S max_char) if_goto_idx)).
    {intros cH. destruct cH as [m [m']]. exists (m' + m). 
     rewrite StringLangProperties.compute_program_add. auto. }
    exists 1. simpl. rewrite p_str_decomposition, nth_error_app2 by lia.
    rewrite <- p_str_decomposition.
    rewrite H_length, PeanoNat.Nat.sub_diag. simpl.
    rewrite H_state_str. simpl.
    simpl in p_str_decomposition.
    remember  (length (get_if_macro_label x opt_label max_char if_goto_idx))
     as if_length.
    replace (pos_str + S if_length) with (pos_str + 1 + if_length) by lia.
    rewrite Heqif_length. 
    rewrite LanguagesUtils.cons_app_assoc in p_str_decomposition.
    rewrite app_assoc in p_str_decomposition.
    remember  ((h ++ [StringLang.Instr opt_label
    (StringLang.IF_ENDS_GOTO x (S max_char) (A (S (max_char + if_goto_idx))))])) as h'.
    apply IHmax_char with 
    (h := h') (t := t); auto.
    rewrite Heqh', length_app, H_length.
    reflexivity.
Qed.

Lemma labeled_instr_if_macro_false : forall x label_idx max_char if_goto_idx n,
  n <> label_idx ->

  StringUtils.has_labeled_instr
    (get_if_macro_label x (Some (A label_idx)) max_char if_goto_idx)
    (A n) =
  false.
Proof.
  intros. rewrite <- PeanoNat.Nat.eqb_neq in H. induction max_char;
  simpl; rewrite H; auto.
Qed.

