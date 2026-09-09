From Triq Require StringLang.
From Triq Require Import StringMacros.

From Triq Require Import LanguagesCommon.
From Triq Require IfMacroProperties.
From Triq Require Import MacroTactics.


From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith Lia.


From AAC_tactics Require Import AAC.
From AAC_tactics Require Instances.
Import Instances.Lists.

Import ListNotations.




Lemma compute_char_transfer :
  forall max_char p_str pos_str state_str 
         label_idx x z goto_label if_goto_idx
         h t skip_block aux char s,



  p_str = h ++
  (get_if_macro_label x (Some (A label_idx)) max_char if_goto_idx ++
  [StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 goto_label)]) ++
  skip_block ++
  get_all_di_blocks x z aux max_char if_goto_idx (A label_idx) ++ t ->

  StringUtils.labels_greater_than skip_block 
  (max_char + if_goto_idx) ->

  StringUtils.labels_less_than h  if_goto_idx ->

  label_idx < if_goto_idx ->

  length h = pos_str  ->

  state_str x = char :: s ->

  char <= max_char ->
  StringLang.ends_with (state_str aux) 0 = true ->


  eqb_var x z = false ->
  eqb_var x aux = false ->
  eqb_var z aux = false ->


  exists n,
  let (line_str, state_str') :=
    StringLang.split_snap
      (StringLang.compute_program p_str (StringLang.SNAP pos_str state_str)
         n) in

  line_str = StringLang.get_labeled_instr p_str (A label_idx) /\
  state_str' x = s /\
  state_str' z =  (state_str z) ++ [char] /\
  forall var, 
  (var <> x /\ var <> z) ->
  state_str' var = state_str var.
Proof.
  induction max_char;
  intros p_str pos_str state_str label_idx x z goto_label
  if_goto_idx h t skip_block aux char s;
  intros p_str_decomposition labels_gt_skip labels_lt_if_goto
  label_idx_lt_if_goto H_length  H_x_value char_leq_max_char 
  ends_with_aux_0 x_diff_z x_diff_aux z_diff_aux.
  - rewrite p_str_decomposition.
    simpl in *. replace (if_goto_idx + 0) with if_goto_idx in * by lia.
    rewrite <- p_str_decomposition.
    assert (char = 0) as char_eq_0 by lia.
    assert (StringLang.ends_with (state_str x) 0 = true) as x_ends_0.
    { rewrite  H_x_value. simpl. rewrite char_eq_0. reflexivity. } 
    rewrite <- H_length in *.
    exists 4.
    rewrite p_str_decomposition. simpl.
    progress_step.
    rewrite x_ends_0. simpl. 
    repeat (progress_step).
    (* Verificação para voltar para linha inicial *)
    assert (StringLang.ends_with (StringLang.append 0 
    (StringLang.del state_str x) z aux) 0 = true) as ends_with_new_0.
    { solve_var_equation. }
    rewrite ends_with_new_0.
    repeat (split; auto).
    + solve_var_equation. rewrite H_x_value. reflexivity.
    + solve_var_equation. rewrite char_eq_0. reflexivity.
    + intros var [var_diff_x var_diff_z].
      apply var_eqb_neq in var_diff_z. apply var_eqb_neq in var_diff_x.
      solve_var_equation.

  (* Passo *)
  - (* Dois casos. Se o caractere é S max_char, vai ser quase igual a base. 
       Se for <= max_char, então ando um passo e uso a hipótese de indução *)
    assert (char = S max_char \/ char <= max_char) as char_cases by lia.
    destruct char_cases as [char_eq_S | char_le_max_char].
    + (* caso char = S max_char -> voltamos em quatro passos *)
      exists 4. rewrite p_str_decomposition.
      simpl. rewrite <- H_length in *.
      repeat (progress_step).
      assert (StringLang.ends_with (state_str x) (S max_char) = true)
      as ends_with_max.
      { rewrite H_x_value, char_eq_S. simpl. clean_nat_eqb. reflexivity. }
      rewrite ends_with_max.
      repeat (progress_step).
      assert (StringLang.ends_with (StringLang.append (S max_char) 
      (StringLang.del state_str x) z aux) 0 = true).
      {solve_var_equation.  } rewrite H.
      rewrite char_eq_S.
      repeat (split; auto); solve_var_equation.
      ++ rewrite H_x_value; reflexivity.
      ++ intros var [var_diff_x var_diff_z]. 
         rewrite <- var_eqb_neq in var_diff_x.
         rewrite <- var_eqb_neq in var_diff_z.
         solve_var_equation.
    + (* Passo, executo 1 passo + IH *)
      cut (exists n n' : nat, 
      let (line_str, state_str') := StringLang.split_snap
      (StringLang.compute_program p_str (StringLang.compute_program p_str 
      (StringLang.SNAP pos_str state_str) n) n') in 
      line_str = StringLang.get_labeled_instr p_str (A label_idx) /\
      state_str' x = s /\
      state_str' z = state_str z ++ [char] /\
      (forall var : variable,
       var <> x /\ var <> z -> state_str' var = state_str var)).
      {intros cH. destruct cH as [m [m']]. exists (m' + m). 
       rewrite StringLangProperties.compute_program_add. auto. } 
      Opaque get_di_block.
      exists 1. rewrite p_str_decomposition. rewrite <- H_length.
      repeat (progress_step).
      rewrite LanguagesUtils.cons_app_assoc.
      repeat (rewrite app_assoc).
      remember (h ++ [StringLang.Instr (Some (A label_idx))
      (StringLang.IF_ENDS_GOTO x (S max_char) 
      (A (S (max_char + if_goto_idx))))]) as h'.
      repeat (rewrite <- app_assoc).
      remember (skip_block ++ get_di_block x z aux if_goto_idx 
       (S max_char) (A label_idx)) as skip_block'.
      assert ((skip_block ++ ((get_di_block x z aux if_goto_idx 
      (S max_char) (A label_idx)) ++ 
      ((get_all_di_blocks x z aux max_char if_goto_idx (A label_idx)) ++
      t))) = skip_block' ++ get_all_di_blocks x z aux max_char 
      if_goto_idx (A label_idx) ++ t) as rewrite_skip_block.
      { rewrite Heqskip_block'. repeat (rewrite <- app_assoc). reflexivity. }
      rewrite rewrite_skip_block.
      rewrite H_x_value. 
      simpl.
      assert (Nat.eqb char (S max_char) = false) as eqb_char_S_max_false.
      { rewrite PeanoNat.Nat.eqb_neq. lia. }
      rewrite eqb_char_S_max_false.
      remember (pos_str + 1) as pos_str'.
      apply IHmax_char with goto_label if_goto_idx h' t skip_block' aux;
      auto.
      ++ rewrite <- app_assoc. reflexivity.
      ++ rewrite Heqskip_block'. Transparent get_di_block. 
         unfold get_di_block. simpl.
         apply StringUtils.labels_greater_than_app; auto.
         * apply StringUtils.labels_greater_than_S; auto.
         * simpl. lia.
      ++ rewrite Heqh'. apply StringUtils.labels_less_than_app; auto.
         simpl. lia.
      ++ rewrite Heqh'. rewrite length_app. simpl.
         reflexivity.
Qed.

Lemma compute_transfer_block_aux :
  forall max_char p_str pos_str state_str 
         label_idx x z goto_label if_goto_idx
         h t aux x_value ,

  p_str = h ++
  (get_if_macro_label x (Some (A label_idx)) max_char if_goto_idx ++
  [StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 goto_label)]) ++
  get_all_di_blocks x z aux max_char if_goto_idx (A label_idx) ++ t ->

  StringUtils.labels_less_than h if_goto_idx ->
  StringUtils.labels_less_than h label_idx ->

  label_idx < if_goto_idx ->
  length h = pos_str  ->

  StringLang.state_over state_str max_char ->
  state_str x = x_value ->
  StringLang.ends_with (state_str aux) 0 = true ->

  eqb_var x z = false ->
  eqb_var x aux = false ->
  eqb_var z aux = false ->


  exists n,
  let (line_str, state_str') :=
    StringLang.split_snap
      (StringLang.compute_program p_str (StringLang.SNAP pos_str state_str)
         n) in

  line_str = StringLang.get_labeled_instr p_str goto_label /\
  state_str' x = [] /\
  state_str' z =  (state_str z) ++ (state_str x) /\
  (* todo o resto do estado está inalterado *)
  forall var, 
  (var <> x /\ var <> z) ->
  state_str' var = state_str var.
Proof.
  intros max_char p_str pos_str state_str label_idx x z 
  goto_label if_goto_idx h t aux x_value.
  intros p_str_decomposition h_less_than_if_goto_idx
  h_less_than_label_idx label_idx_lt_if_goto H_length H_state_over 
  H_x_value ends_with_aux
  x_diff_z x_diff_aux z_diff_aux.
  generalize dependent state_str.
  induction x_value as [| char s];
  intros state_str H_state_over H_x_value ends_with_aux.
  - cut (exists n n' : nat, 
      let (line_str, state_str') := StringLang.split_snap
      (StringLang.compute_program p_str (StringLang.compute_program p_str 
      (StringLang.SNAP pos_str state_str) n) n') in 
      line_str = StringLang.get_labeled_instr p_str goto_label /\
      state_str' x = [] /\
      state_str' z = state_str z ++ state_str x /\
      (forall var : variable,
       var <> x /\ var <> z -> state_str' var = state_str var)).
    {intros cH. destruct cH as [m [m']]. exists (m' + m). 
       rewrite StringLangProperties.compute_program_add. auto. }
    rewrite <- app_assoc in p_str_decomposition.
    remember ([StringLang.Instr None 
    (StringLang.IF_ENDS_GOTO aux 0 goto_label)] ++ 
    get_all_di_blocks x z aux max_char if_goto_idx (A label_idx) ++ t)
    as t'.
    pose proof (IfMacroProperties.compute_if_block_label_skip 
    max_char p_str pos_str state_str x (Some (A label_idx)) 
    if_goto_idx h t') as if_skip.
    destruct if_skip as [if_skip_steps H_if_skip]; auto.
    exists if_skip_steps. destruct (StringLang.compute_program p_str 
    (StringLang.SNAP pos_str state_str) if_skip_steps) as [if_line if_state].
    simpl in *. destruct H_if_skip as [H_if_state H_if_line].
    rewrite H_if_state, H_if_line. rewrite p_str_decomposition.
    exists 1. simpl. rewrite <- H_length.
    repeat (progress_step).
    rewrite Heqt'. simpl. rewrite ends_with_aux.
    simpl. repeat (split; auto).
    rewrite H_x_value. rewrite app_nil_r. reflexivity.
  - pose proof (H_state_over x) as state_str_x_over.
    rewrite H_x_value in state_str_x_over.
    simpl in state_str_x_over. destruct state_str_x_over as 
    [char_leq_max_char string_over_s].
    cut (exists n n' : nat, 
      let (line_str, state_str') := StringLang.split_snap
      (StringLang.compute_program p_str (StringLang.compute_program p_str 
      (StringLang.SNAP pos_str state_str) n) n') in 
      line_str = StringLang.get_labeled_instr p_str goto_label /\
      state_str' x = [] /\
      state_str' z = state_str z ++ state_str x /\
      (forall var : variable,
       var <> x /\ var <> z -> state_str' var = state_str var)).
    {intros cH. destruct cH as [m [m']]. exists (m' + m). 
       rewrite StringLangProperties.compute_program_add. auto. }
    assert (exists n : nat, let (line_str, state_str') :=
    StringLang.split_snap (StringLang.compute_program p_str 
    (StringLang.SNAP pos_str state_str) n) in
    line_str = StringLang.get_labeled_instr p_str (A label_idx) /\
    state_str' x = s /\
    state_str' z = state_str z ++ [char] /\
    (forall var : variable,
     var <> x /\ var <> z -> state_str' var = state_str var)) as 
    [char_transfer_steps H_char_transfer].
     { apply compute_char_transfer with max_char goto_label
       if_goto_idx h t [] aux; simpl; auto. }
    exists char_transfer_steps. destruct (StringLang.compute_program
    p_str (StringLang.SNAP pos_str state_str) char_transfer_steps)
    as [char_transfer_line char_transfer_state].
    simpl in H_char_transfer.
    destruct H_char_transfer as [char_line [char_state_x [char_state_z
    char_inv]]].
    assert (char_transfer_line = pos_str) as char_transfer_pos.
    { rewrite char_line, p_str_decomposition.
      rewrite StringUtils.get_labeled_instr_app.
      + destruct max_char; simpl; 
        rewrite PeanoNat.Nat.eqb_refl, H_length; lia.
      + apply StringUtils.labels_less_implies_diff with (label_idx);
        auto. }
    rewrite char_transfer_pos.
    specialize (IHs char_transfer_state).
    assert (StringLang.state_over char_transfer_state max_char) as
    transfer_state_over.
    { unfold StringLang.state_over. intros x0. 
      destruct (var_eqb_dec x0 x) as [x0_eq_x | x0_diff_x].
      + rewrite x0_eq_x, char_state_x; auto.
      + destruct (var_eqb_dec x0 z) as [x0_eq_z | x0_diff_z].
        ++ rewrite x0_eq_z, char_state_z. StringLang.solve_string.
        ++ replace (char_transfer_state x0) with (state_str x0).
           auto. symmetry. apply char_inv. auto. }
    assert (StringLang.ends_with (char_transfer_state aux) 0 = true) as
    ends_with_transfer_aux.
    { assert (aux <> x /\ aux <> z) as aux_diff_x_z. split.
      + symmetry. rewrite <- var_eqb_neq; auto.
      + symmetry. rewrite <- var_eqb_neq; auto.
      + apply char_inv in aux_diff_x_z. rewrite aux_diff_x_z.
        auto. }
    destruct IHs as [IHsteps IHs ]; auto.
    exists IHsteps. destruct (StringLang.compute_program p_str
    (StringLang.SNAP pos_str char_transfer_state) IHsteps) as 
    [IHline IHstate]; simpl in *.
    destruct IHs as [IHline_eq [IHstate_x_eq [IHstate_z_eq IH_inv]]]. 
    repeat (split; auto).
    + rewrite IHstate_z_eq, char_state_z, char_state_x, H_x_value.
      rewrite <- app_assoc. reflexivity.
    + intros var var_diff_x_z. rewrite IH_inv; auto.
Qed.


Lemma compute_transfer_block :
  forall max_char p_str pos_str state_str 
         label_idx x z goto_label if_goto_idx
         h t aux x_value ,

  p_str = h ++
      transfer_block (A label_idx) x z if_goto_idx goto_label aux max_char
   ++ t ->

  StringUtils.labels_less_than h if_goto_idx ->
  StringUtils.labels_less_than h label_idx ->

  label_idx < if_goto_idx ->
  length h = pos_str  ->

  StringLang.state_over state_str max_char ->
  state_str x = x_value ->
  StringLang.ends_with (state_str aux) 0 = true ->

  eqb_var x z = false ->
  eqb_var x aux = false ->
  eqb_var z aux = false ->


  exists n,
  let (line_str, state_str') :=
    StringLang.split_snap
      (StringLang.compute_program p_str (StringLang.SNAP pos_str state_str)
         n) in

  line_str = StringLang.get_labeled_instr p_str goto_label /\
  state_str' x = [] /\
  state_str' z =  (state_str z) ++ (state_str x) /\
  (* todo o resto do estado está inalterado *)
  forall var, 
  (var <> x /\ var <> z) ->
  state_str' var = state_str var.
Proof.
  intros. unfold transfer_block in *. rewrite H. apply compute_transfer_block_aux
  with max_char label_idx if_goto_idx h t aux x_value; eauto.
  aac_reflexivity. 
Qed.