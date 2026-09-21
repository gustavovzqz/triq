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


Lemma compute_char_incr_aux :
  forall max_char p_str pos_str state_str 
         label_idx x z if_goto_idx
         h t goto_label skip_block aux char s,

  p_str = h ++
  get_if_macro_label x (Some (A label_idx)) max_char if_goto_idx ++
  skip_block ++
  get_all_ai_blocks_incr x z aux max_char if_goto_idx goto_label ++ t ->

  StringUtils.labels_greater_than skip_block 
  (max_char + if_goto_idx) ->

  StringUtils.labels_less_than h if_goto_idx ->

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

  (line_str = StringLang.get_labeled_instr p_str goto_label /\
  state_str' x = s /\
  state_str' z =  (state_str z) ++ [char + 1]) /\
  forall var, 
  (var <> x /\ var <> z) ->
  state_str' var = state_str var.
Proof.
  induction max_char; 
  intros p_str pos_str state_str label_idx x z if_goto_idx h t 
  goto_label skip_block aux char s;
  intros p_str_decomposition label_ge_skip labels_lt_h label_lt_goto 
  H_length H_x_value char_le_max ends_with_aux x_diff_z x_diff_aux z_diff_aux.
  + rewrite p_str_decomposition. simpl. rewrite <- H_length.
    assert (char = 0) as char_eq_0 by lia.
    exists 4. simpl.
    repeat (progress_step).
    rewrite H_x_value. replace (char) with 0 by lia. simpl.
    repeat (progress_step).
    assert (StringLang.ends_with
    (StringLang.append 1 (StringLang.del state_str x) z aux) 0 = true)
    as ends_with_steps_true.
    { unfold StringLang.append, StringLang.del, StringLang.update.
      rewrite z_diff_aux, x_diff_aux, ends_with_aux. reflexivity. }
    rewrite ends_with_steps_true.
    simpl. repeat (split; auto); solve_var_equation.
    ++ rewrite H_x_value. reflexivity.
    ++ intros var [var_diff_x var_diff_z]. rewrite <- var_eqb_neq in *.
       solve_var_equation.
  + assert (char = S max_char \/ char <> S max_char) as char_cases by lia.
    destruct char_cases as [char_eq_S | char_diff_S].
    ++ exists 4. rewrite p_str_decomposition. rewrite <- H_length.
       repeat (progress_step).
       rewrite H_x_value. simpl. rewrite char_eq_S, PeanoNat.Nat.eqb_refl.
       repeat (progress_step).
       assert (StringLang.ends_with (StringLang.append  (S (max_char + 1)) 
       (StringLang.del state_str x) z aux) 0 = true) as ends_with_true
       by  solve_var_equation. 
       rewrite ends_with_true. simpl. repeat (split; auto); solve_var_equation.
       * rewrite H_x_value. reflexivity.
       * intros var [var_diff_x var_diff_z].
         rewrite <- var_eqb_neq in *. solve_var_equation.
         
    ++ cut (exists n n' : nat, 
       let (line_str, state_str') := StringLang.split_snap
       (StringLang.compute_program p_str (StringLang.compute_program p_str 
       (StringLang.SNAP pos_str state_str) n) n') 
       in (line_str = StringLang.get_labeled_instr p_str goto_label /\
       state_str' x = s /\ state_str' z = state_str z ++ [char + 1]) /\
       (forall var : variable,
       var <> x /\ var <> z -> state_str' var = state_str var)).
       {intros cH. destruct cH as [m [m']]. exists (m' + m). 
       rewrite StringLangProperties.compute_program_add. auto. }
       rewrite <- H_length. rewrite p_str_decomposition. 
       exists 1. repeat (progress_step).
       assert (StringLang.ends_with (state_str x) 
       (S max_char) = false) as ends_with_S.  
       { rewrite H_x_value. simpl. rewrite PeanoNat.Nat.eqb_neq. lia.  } 
       rewrite ends_with_S. 
       repeat (rewrite cons_app_assoc). rewrite app_assoc.
       remember (h ++ [StringLang.Instr (Some (A label_idx)) (StringLang.IF_ENDS_GOTO x 
       (S max_char) (A (S (max_char + if_goto_idx))))]) as h'.
       set (skip_block ++ [StringLang.Instr (Some 
       (A (if_goto_idx + S max_char))) (StringLang.DEL x)] ++
       [StringLang.Instr None (StringLang.APPEND (S (max_char + 1)) z)] ++
       [StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 goto_label)])
       as skip_block'. apply IHmax_char with label_idx if_goto_idx h' t
       skip_block' aux; auto.
       * unfold skip_block'. simpl. repeat (rewrite cons_app_assoc).
         repeat (rewrite <- app_assoc). simpl. reflexivity.
       * unfold skip_block'. apply StringUtils.labels_greater_than_app.
         ** apply StringUtils.labels_greater_than_S. 
            replace (S (max_char + if_goto_idx)) with 
            (S max_char + if_goto_idx) by lia. auto.
         ** simpl. lia.
      * rewrite Heqh'. apply StringUtils.labels_less_than_app; auto.
        simpl; lia.
      * rewrite Heqh'. rewrite length_app. reflexivity.
      * lia.
Qed.


Lemma compute_char_incr :
  forall max_char p_str pos_str state_str 
          x z label_idx goto_label if_goto_idx h t aux char s T2,

  p_str = h ++
  get_if_macro_label x (Some (A (label_idx))) max_char if_goto_idx ++ 
  ([StringLang.Instr None (StringLang.APPEND 0 z)] ++ 
  [StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 goto_label)]) ++

  [StringLang.Instr (Some (A (if_goto_idx + max_char))) (StringLang.DEL x)] ++
   [StringLang.Instr None (StringLang.APPEND 0 z)] ++
   [StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 (A label_idx))] ++

  get_all_incr_blocks x z aux max_char if_goto_idx T2 ++ t ->

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
    StringLang.split_snap
      (StringLang.compute_program p_str (StringLang.SNAP pos_str state_str)
         n) in

  (if (PeanoNat.Nat.eqb char max_char) then 
    (line_str = StringLang.get_labeled_instr p_str (A label_idx) /\
    state_str' x = s /\
    state_str' z =  (state_str z) ++ [0])
  else 
    (line_str = StringLang.get_labeled_instr p_str T2 /\
     state_str' x = s /\
     state_str' z = (state_str z) ++ [char + 1])) 
  /\
  forall var, 
  (var <> x /\ var <> z) ->
  state_str' var = state_str var.
Proof.
  destruct max_char; intros p_str pos_str state_str x z label_idx goto_label
  if_goto_idx h t aux char s T2;
  intros p_str_decomposition less_than_H H_length H_x_value label_le 
  char_leq_max ends_with_aux x_diff_z x_diff_aux z_diff_aux.
  - assert (char = 0) as char_eq_0 by lia. 
    rewrite char_eq_0, PeanoNat.Nat.eqb_refl.
    simpl in p_str_decomposition. replace (if_goto_idx + 0) with if_goto_idx
    in p_str_decomposition by lia. rewrite p_str_decomposition.
    exists 4. simpl. rewrite <- H_length.
    repeat (progress_step).
    rewrite H_x_value, char_eq_0. simpl.
    repeat (progress_step).
    assert (StringLang.ends_with  (StringLang.append 0 
    (StringLang.del state_str x) z aux) 0 = true) as ends_with_true by solve_var_equation.
    rewrite ends_with_true. simpl. repeat (split; auto); solve_var_equation.
    + rewrite H_x_value. reflexivity.
    + intros var [var_diff_x var_diff_z].
      rewrite <- var_eqb_neq in *. solve_var_equation.

  - simpl. assert (char = S max_char \/ char <> S max_char) as 
    char_cases by lia.
    destruct char_cases as [char_eq_S | char_diff_S].
    + rewrite char_eq_S, PeanoNat.Nat.eqb_refl.
      exists 4. rewrite p_str_decomposition. rewrite <- H_length.
      repeat (progress_step).
      rewrite H_x_value, char_eq_S. simpl. rewrite PeanoNat.Nat.eqb_refl.
      repeat (progress_step).
      assert (StringLang.ends_with (StringLang.append 0 (StringLang.del 
      state_str x) z aux) 0 = true) as ends_with_true.
      { unfold StringLang.append, StringLang.del, StringLang.update. 
        rewrite z_diff_aux, x_diff_aux, ends_with_aux. reflexivity. }
      rewrite ends_with_true. repeat (split; auto); solve_var_equation.
      ++ rewrite H_x_value; reflexivity.
      ++ intros var [var_diff_x var_diff_z].
         rewrite <- var_eqb_neq in *. solve_var_equation.
        
    + assert (PeanoNat.Nat.eqb char (S max_char) = false).
      { rewrite PeanoNat.Nat.eqb_neq. lia. } rewrite H.
      cut (exists n n' : nat, 
      let (line_str, state_str') := StringLang.split_snap
      (StringLang.compute_program p_str (StringLang.compute_program p_str 
      (StringLang.SNAP pos_str state_str) n) n') 
      in (line_str = StringLang.get_labeled_instr p_str T2 /\
      state_str' x = s /\ state_str' z = state_str z ++ [char + 1]) /\
      (forall var : variable,
      var <> x /\ var <> z -> state_str' var = state_str var)).
      {intros cH. destruct cH as [m [m']]. exists (m' + m). 
       rewrite StringLangProperties.compute_program_add. auto. }
      simpl in p_str_decomposition.

      rewrite p_str_decomposition. rewrite <- H_length. 
      exists 1. repeat (progress_step).
      assert (StringLang.ends_with (state_str x) (S max_char) = false) as ends_with_S.
      { rewrite H_x_value. simpl. auto. } simpl. rewrite ends_with_S. 
      rewrite <- p_str_decomposition.
      repeat (rewrite cons_app_assoc in p_str_decomposition).
      rewrite app_assoc in p_str_decomposition.
      set ((h ++ [StringLang.Instr (Some (A label_idx)) 
      (StringLang.IF_ENDS_GOTO  x (S max_char) 
      (A (S (max_char + if_goto_idx))))])) as h'. 
      simpl in p_str_decomposition.
      set ([StringLang.Instr None (StringLang.APPEND 0 z);
            StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 goto_label);
            StringLang.Instr (Some (A (if_goto_idx + (S max_char)))) 
            (StringLang.DEL x);
            (StringLang.Instr None (StringLang.APPEND 0 z));
            (StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 
            (A label_idx)))]) as 
      skip_block.
      assert (p_str = h' ++ get_if_macro_label x (Some (A label_idx)) 
      max_char (if_goto_idx) ++ skip_block ++ get_all_ai_blocks_incr 
      x z aux max_char if_goto_idx T2 ++ t) as p_str_eq.
      { rewrite p_str_decomposition. unfold h', skip_block.
        simpl. repeat (rewrite cons_app_assoc). 
        repeat (rewrite <- app_assoc). reflexivity. }
      repeat (rewrite cons_app_assoc in p_str_decomposition).
      rewrite <- app_assoc in p_str_decomposition.
      apply compute_char_incr_aux with max_char  label_idx
      if_goto_idx h' t skip_block aux; auto.
      ++ unfold skip_block. simpl. lia.
      ++ unfold h'. apply StringUtils.labels_less_than_app; auto.
         simpl. lia.
      ++ unfold h'. rewrite length_app. reflexivity.
      ++ lia.
Qed.

Lemma compute_incr_macro_aux :
  forall max_char p_str pos_str state_str 
         instr_label x 
         max_label_nat max_z_nat  h t x_value, 

  let max_label_str := StringUtils.get_max_label h in 

  p_str = h ++
  StringMacros.get_str_macro 
  (NatLang.Instr instr_label (NatLang.INCR x)) 
  max_char max_label_nat max_z_nat
  max_label_str ++ t  ->

  length h = pos_str  ->

  label_lt_idx instr_label max_label_nat ->

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
  (max_label_nat + max_label_str + max_char + max_char + 5)) /\  
  state_str' x = []  /\
  state_str' (Z (max_z_nat + 1)) = state_str (Z (max_z_nat + 1)) 
             ++ incr_string (state_str x) max_char /\
  forall var, 
  var <> x /\ var <> (Z (max_z_nat + 1)) ->
  state_str' var = state_str var.
Proof.
  intros max_char p_str pos_str state_str instr_label x 
  max_label_nat max_z_nat h t x_value.
  intros max_label_str p_str_decomposition H_length label_lt_max_nat
  H_state_over string_over_x_value H_x_value H_aux_value 
  x_diff_z x_diff_aux.


  (* Indução em x_value *)

  generalize dependent state_str. induction x_value ; 
  intros state_str H_state_over H_x_value H_aux_value.
  - cut (exists n n' : nat, 
    let (line_str, state_str') := StringLang.split_snap
    (StringLang.compute_program p_str (StringLang.compute_program p_str 
    (StringLang.SNAP (pos_str + 1) state_str) n) n') in 
     line_str = StringLang.get_labeled_instr p_str (A 
    (max_label_nat + max_label_str + max_char + max_char + 5)) /\  
    state_str' x = []  /\
    state_str' (Z (max_z_nat + 1)) = state_str (Z (max_z_nat + 1)) 
              ++ incr_string (state_str x) max_char /\
    forall var, 
    var <> x /\ var <> (Z (max_z_nat + 1)) ->
    state_str' var = state_str var).
    {intros cH. destruct cH as [m [m']]. exists (m' + m). 
       rewrite StringLangProperties.compute_program_add. auto. }
    unfold get_str_macro in p_str_decomposition.
    unfold get_incr_macro in p_str_decomposition.

    set ([StringLang.Instr None (StringLang.APPEND 0 (Z (max_z_nat + 1)))] ++
      [StringLang.Instr None (StringLang.IF_ENDS_GOTO (Z (max_z_nat + 2)) 0 (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 +
      max_char + 1)))] ++
      [StringLang.Instr (Some (A (max_label_nat + max_label_str + 1 + 1 + max_char))) (StringLang.DEL x)] ++
      [StringLang.Instr None (StringLang.APPEND 0 (Z (max_z_nat + 1)))] ++
      [StringLang.Instr None (StringLang.IF_ENDS_GOTO (Z (max_z_nat + 2)) 0 (A (max_label_nat + max_label_str + 1)))] ++
      get_all_incr_blocks x (Z (max_z_nat + 1)) (Z (max_z_nat + 2)) max_char (max_label_nat + max_label_str + 1 + 1)
      (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1)) ++
      transfer_block (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1)) x (Z (max_z_nat + 1))
      (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1) (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + max_char + 1))
      (Z (max_z_nat + 2)) max_char ++
      transfer_block (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + max_char + 1)) (Z (max_z_nat + 1)) x
      (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + max_char + 1 + 1)
      (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + max_char + 1 + 1 + max_char + 1)) (Z (max_z_nat + 2)) max_char ++
      [StringLang.Instr (Some (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + max_char + 1 + 1 + max_char + 1)))
      (StringLang.DEL (Z (max_z_nat + 2)))] ++ t) as t'.


    set (h ++ [StringLang.Instr instr_label 
    (StringLang.APPEND 0 (Z (max_z_nat + 2)))]) as h'.
    pose proof (IfMacroProperties.compute_if_block_label_skip max_char p_str (pos_str + 1)
    state_str x (Some (A (max_label_nat + max_label_str + 1))) 
    (max_label_nat + max_label_str + 1 + 1) h' t' )  as if_skip.
    destruct if_skip as [if_skip_steps H_if_skip]; auto.
    rewrite p_str_decomposition. unfold h', t'. aac_reflexivity. 
    unfold h'. rewrite length_app, H_length. simpl. reflexivity. 
    clear t'. clear h'.
    exists if_skip_steps. destruct (StringLang.compute_program p_str 
    (StringLang.SNAP (pos_str + 1) state_str) if_skip_steps).
    simpl in H_if_skip. destruct H_if_skip as [s_eq n_eq].
    rewrite s_eq. rewrite n_eq.

    exists 2. rewrite <- H_length. simpl. rewrite p_str_decomposition.
    repeat (progress_step).
    assert (StringLang.ends_with (StringLang.append 0 
    state_str (Z (max_z_nat + 1)) (Z (max_z_nat + 2))) 0 = true ) 
    as ends_with_true. { solve_var_equation. simpl.
    replace (Nat.eqb (max_z_nat + 1) (max_z_nat + 2)) with false.
    rewrite H_aux_value. reflexivity. symmetry. rewrite PeanoNat.Nat.eqb_neq.
    lia. } rewrite ends_with_true.
    repeat (progress_step). simpl in p_str_decomposition.
    repeat (split; auto).
    + f_equal. replace ((max_label_nat + (max_label_str + 
    S (S (max_char + S (S (max_char + 1))))))) with 
    (max_label_nat + (max_label_str + (max_char + (max_char + 5))))
    by lia. reflexivity.
    + solve_var_equation. rewrite H_x_value. reflexivity.
    + solve_var_equation. rewrite H_x_value. reflexivity.
    + intros var [var_diff_x var_diff_z].
      rewrite <- var_eqb_neq in *. solve_var_equation.
  - (* Dividindo em dois passos. *)
    cut (exists n n' : nat, 
    let (line_str, state_str') := StringLang.split_snap
    (StringLang.compute_program p_str (StringLang.compute_program p_str 
    (StringLang.SNAP (pos_str + 1) state_str) n) n') in 
     line_str = StringLang.get_labeled_instr p_str (A 
    (max_label_nat + max_label_str + max_char + max_char + 5)) /\  
    state_str' x = []  /\
    state_str' (Z (max_z_nat + 1)) = state_str (Z (max_z_nat + 1)) 
              ++ incr_string (state_str x) max_char /\
    forall var, 
    var <> x /\ var <> (Z (max_z_nat + 1)) ->
    state_str' var = state_str var).
    {intros cH. destruct cH as [m [m']]. exists (m' + m). 
       rewrite StringLangProperties.compute_program_add. auto. }
    unfold get_str_macro in p_str_decomposition.
    unfold get_incr_macro in p_str_decomposition.

    set (h ++ [StringLang.Instr instr_label (StringLang.APPEND 0 (Z (max_z_nat + 2)))])
    as h'.

    set (transfer_block (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1)) x (Z (max_z_nat + 1))
        (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1)
        (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + max_char + 1)) (Z (max_z_nat + 2))
        max_char ++
        transfer_block (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + max_char + 1))
        (Z (max_z_nat + 1)) x (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + max_char + 1 + 1)
        (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + max_char + 1 + 1 + max_char + 1))
        (Z (max_z_nat + 2)) max_char ++
        [StringLang.Instr
        (Some (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + max_char + 1 + 1 + max_char +
        1))) (StringLang.DEL (Z (max_z_nat + 2)))] ++ t) as t'.

    assert (a = max_char \/ a < max_char) as max_char_diff.
    {simpl in string_over_x_value. lia. }

    pose proof (compute_char_incr max_char p_str  (pos_str + 1) 
    state_str x (Z (max_z_nat + 1)) (max_label_nat + max_label_str + 1)                               
    (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + max_char + 1))
    (max_label_nat + max_label_str + 1 + 1) h' t' (Z (max_z_nat + 2))
    a x_value (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1))) 
    as H_char_incr.
    
    destruct H_char_incr as [char_incr_steps H_char_incr]; auto; try lia.
    + unfold h', t'. rewrite p_str_decomposition. repeat (rewrite cons_app_assoc). 
      repeat (rewrite app_nil_r).
      aac_reflexivity.
    + unfold h'. apply StringUtils.labels_less_than_app.
      ++ apply StringUtils.labels_leq_max. unfold max_label_str. lia.
      ++ simpl. destruct instr_label; auto.
         destruct l. simpl in label_lt_max_nat. lia.
    + unfold h'. rewrite length_app, H_length. reflexivity.
    + rewrite H_aux_value; reflexivity.
    + simpl. rewrite PeanoNat.Nat.eqb_neq. lia.
    + exists char_incr_steps. simpl in H_char_incr.
      (* Se for max_char, volto e aplico IH, se for diferente,
         vou para T1, executo, e chego em T2. *)
      destruct max_char_diff.
      * rewrite H in H_char_incr. rewrite PeanoNat.Nat.eqb_refl in H_char_incr.
        destruct (StringLang.compute_program p_str (StringLang.SNAP (pos_str + 1) state_str)
        char_incr_steps). simpl in H_char_incr.
        destruct H_char_incr as [[n_eq [sx_eq sz_eq]] forall_eq].
        rewrite n_eq. (* Aplicar IHx_value *) 
        assert (StringLang.get_labeled_instr p_str 
        (A (max_label_nat + max_label_str + 1)) = pos_str + 1).
        { rewrite p_str_decomposition, StringUtils.get_labeled_instr_app.
          + simpl. assert (Nat.eqb (max_label_nat + max_label_str + 1)
            (max_label_nat + max_label_str + 1) = true).
            {rewrite PeanoNat.Nat.eqb_eq. lia. }
            destruct instr_label.
            ++ destruct l. simpl. simpl in label_lt_max_nat.
               replace (Nat.eqb n0 (max_label_nat + max_label_str + 1))
               with false. simpl. 
               destruct max_char; simpl; rewrite H0; auto.
               symmetry. rewrite PeanoNat.Nat.eqb_neq. lia.
            ++ simpl. destruct max_char; simpl; rewrite H0; auto.
          + apply StringUtils.labels_less_implies_diff
          with (max_label_str + 1); try lia. 
          apply StringUtils.labels_leq_max. unfold max_label_str. lia. } 
          rewrite H0.
        simpl in string_over_x_value. destruct string_over_x_value as
        [a_leq_max string_over_x_value].

        pose proof (IHx_value string_over_x_value s). destruct H1; auto.
        unfold StringLang.state_over. intros x0.
        destruct (var_eqb_dec x x0).
        rewrite <- e. rewrite sx_eq. auto.
        destruct (var_eqb_dec (Z (max_z_nat + 1)) x0).
        rewrite <- e. rewrite sz_eq. apply StringLang.string_over_app.
        auto. auto. auto. simpl. lia.
        replace (s x0) with (state_str x0).
        auto. symmetry. auto. 
        rewrite <- H_aux_value. apply forall_eq.
        repeat (split; auto).
        symmetry. rewrite <- var_eqb_neq. auto.
        injection. intros H2. lia.
        exists x0. 
        destruct ((StringLang.compute_program p_str (StringLang.SNAP (pos_str + 1) s) x0)).
        simpl in *. destruct H1, H2, H3.
        repeat (split; auto).
        ++ rewrite H3. rewrite sz_eq, sx_eq, H_x_value.  
           rewrite H. simpl. rewrite PeanoNat.Nat.ltb_irrefl. 
           rewrite <- app_assoc. simpl. reflexivity.
        ++ intros var [var_diff_x var_diff_z].
           transitivity (s var). auto. auto.
      * (* Andar H_char_incr_steps *)
        assert (PeanoNat.Nat.eqb a max_char = false).
        {rewrite PeanoNat.Nat.eqb_neq. lia. }
        rewrite H0 in H_char_incr.
        destruct (StringLang.compute_program p_str (StringLang.SNAP (pos_str + 1) state_str)
        char_incr_steps). simpl in H_char_incr.
        destruct H_char_incr as [[n_eq [sx_eq sz_eq]] forall_eq].
        (* Preciso executar o transfer *)
        clear h' t'.
        set (h ++
      ([StringLang.Instr instr_label (StringLang.APPEND 0 (Z (max_z_nat + 2)))] ++
      get_if_macro_label x (Some (A (max_label_nat + StringUtils.get_max_label h + 1))) max_char
      (max_label_nat + StringUtils.get_max_label h + 1 + 1) ++
      [StringLang.Instr None (StringLang.APPEND 0 (Z (max_z_nat + 1)))] ++
      [StringLang.Instr None
      (StringLang.IF_ENDS_GOTO (Z (max_z_nat + 2)) 0 (A (max_label_nat + StringUtils.get_max_label h + 1 + 1 + max_char + 1 + 1 +
      max_char + 1)))] ++
      [StringLang.Instr (Some (A (max_label_nat + StringUtils.get_max_label h + 1 + 1 + max_char))) (StringLang.DEL x)] ++
      [StringLang.Instr None (StringLang.APPEND 0 (Z (max_z_nat + 1)))] ++
      [StringLang.Instr None (StringLang.IF_ENDS_GOTO (Z (max_z_nat + 2)) 0 (A (max_label_nat + StringUtils.get_max_label h + 1)))] ++
      get_all_incr_blocks x (Z (max_z_nat + 1)) (Z (max_z_nat + 2)) max_char (max_label_nat + StringUtils.get_max_label h + 1 + 1)
      (A (max_label_nat + StringUtils.get_max_label h + 1 + 1 + max_char + 1)))) as h'.

      set (transfer_block (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + max_char + 1)) (Z (max_z_nat + 1)) x
    (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + max_char + 1 + 1)
    (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + max_char + 1 + 1 + max_char + 1)) (Z (max_z_nat + 2)) max_char ++
    [StringLang.Instr (Some (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + max_char + 1 + 1 + max_char + 1)))
    (StringLang.DEL (Z (max_z_nat + 2)))] ++ t) as t'.
    
        pose proof (TransferMacroProperties.compute_transfer_block
        max_char p_str n s (max_label_nat + max_label_str + 1 + 1 + max_char + 1)
        x (Z (max_z_nat + 1))
        (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 +
        max_char + 1)) (max_label_nat + max_label_str + 1 + 1 + 
        max_char + 1 + 1) h' t' (Z (max_z_nat + 2)) (s x)).
        unfold max_label_str in *.
        destruct H1; auto.
        ** unfold h', t'. rewrite p_str_decomposition. aac_reflexivity.
        ** unfold h'. repeat (solve_less_than_app).
        ** unfold h'. repeat (solve_less_than_app).
        ** lia.
        ** unfold h'. rewrite n_eq, p_str_decomposition.
           repeat (rewrite <- app_assoc).
           repeat(rewrite_labeled_instr_app).
           rewrite get_labeled_instr_transfer.
           repeat (rewrite length_app). lia.
        ** intros x0. destruct (var_eqb_dec x x0).
          rewrite <- e. rewrite sx_eq.
          simpl in string_over_x_value.
          destruct string_over_x_value. auto.
          destruct (var_eqb_dec (Z (max_z_nat + 1)) x0).
          rewrite <- e. rewrite sz_eq. apply StringLang.string_over_app.
          auto. auto. auto. simpl. lia.
          replace (s x0) with (state_str x0).
          auto. symmetry. auto. 
        ** replace (s (Z (max_z_nat + 2))) with [0]. reflexivity.
          rewrite <- H_aux_value. symmetry. apply forall_eq.
          split. symmetry. rewrite <- var_eqb_neq. auto.
          injection; lia.
        ** simpl. rewrite PeanoNat.Nat.eqb_neq; lia.
        ** exists x0. 
        destruct ((StringLang.compute_program p_str (StringLang.SNAP n s)
        x0)). simpl in H1. simpl. 
        destruct H1 as [n0_q [s0_eq [s0_aux forall_eq_]]].
        repeat (split; auto).
        *** rewrite n0_q. f_equal. f_equal. lia.
        *** rewrite s0_aux, sz_eq, sx_eq, H_x_value.
            simpl. replace (Nat.ltb a max_char) with true.
            repeat rewrite <- app_assoc.
            rewrite cons_app_assoc. reflexivity.
            symmetry. rewrite (PeanoNat.Nat.ltb_lt). lia.
        *** intros var [var_diff_x var_diff_z].
            transitivity (s var). auto. auto.
Qed. 

Lemma compute_incr_macro :
  forall max_char p_str pos_str state_str 
         instr_label x 
         max_label_nat max_z_nat  h t x_value, 

  let max_label_str := StringUtils.get_max_label h in 

  p_str = h ++
  StringMacros.get_str_macro 
  (NatLang.Instr instr_label (NatLang.INCR x)) 
  max_char max_label_nat max_z_nat
  max_label_str ++ t  ->

  length h = pos_str  ->

  label_lt_idx instr_label max_label_nat ->

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
  (NatLang.Instr instr_label (NatLang.INCR x)) max_char /\  
  state_str' x = state_str (Z (max_z_nat + 1)) 
             ++ incr_string (state_str x) max_char  /\
  state_str' (Z (max_z_nat + 1)) = [] /\
  forall var, 
  var <> x /\ var <> (Z (max_z_nat + 1)) ->
  state_str' var = state_str var.
Proof.
  intros max_char p_str pos_str state_str instr_label x 
  max_label_nat max_z_nat h t x_value max_label_str.
  intros p_str_decomposition H_length label_lt_max_nat
  H_state_over string_over_x_value H_x_value H_aux_value 
  x_diff_z x_diff_aux.

  (* Executo um passo, depois o lema anterior, depois uma transferência e
     finalmente mais um passo.*)

  cut (exists n n' n'' n''' : nat, 
       let (line_str, state_str') := StringLang.split_snap
       (StringLang.compute_program p_str 
       (StringLang.compute_program p_str 
       (StringLang.compute_program p_str (StringLang.compute_program p_str 
       (StringLang.SNAP pos_str state_str) n) n') n'') n''')
       in 
      
       line_str = pos_str + StringMacros.macro_length 
     (NatLang.Instr instr_label (NatLang.INCR x)) max_char /\
      state_str' x = state_str (Z (max_z_nat + 1)) ++ incr_string (state_str x)
      max_char /\
      state_str' (Z (max_z_nat + 1)) = [] /\
      (forall var : variable,
      var <> x /\ var <> Z (max_z_nat + 1) -> state_str' var = state_str var)).
       {intros cH. destruct cH as [m [m' [m'' [m''']]]]. exists (m''' + m'' + m' + m). 
       rewrite StringLangProperties.compute_program_add. 
       rewrite StringLangProperties.compute_program_add.
       rewrite StringLangProperties.compute_program_add.  auto. }
  (* 1. Em um passo, tenho o valor de aux incrementado em um. *)
  exists 1. simpl in *.
  rewrite p_str_decomposition. rewrite <- H_length.  rewrite nth_error_app2 by lia.
  rewrite PeanoNat.Nat.sub_diag. simpl.
  remember (StringLang.append 0 state_str (Z (max_z_nat + 2)))
  as one_step_state.

  (* 2. Executando os passos *)
  pose proof (compute_incr_macro_aux
  max_char p_str pos_str one_step_state instr_label x max_label_nat max_z_nat
  h t x_value) as H_incr_aux. simpl in H_incr_aux. 
  destruct H_incr_aux as [incr_aux_steps H_incr_aux]; auto.
  rewrite Heqone_step_state. StringLang.solve_string. lia.
  rewrite Heqone_step_state. solve_var_equation. auto.
  rewrite Heqone_step_state. solve_var_equation. rewrite H_aux_value. auto.
  exists incr_aux_steps. rewrite <- p_str_decomposition. 
  rewrite <- H_length in H_incr_aux.
  destruct ((StringLang.compute_program p_str (StringLang.SNAP (length h + 1)
  one_step_state) incr_aux_steps)). simpl. simpl in H_incr_aux.
  destruct H_incr_aux as [Hn [Hsx [Hsz1 Hsforall]]].
  repeat (rewrite cons_app_assoc in p_str_decomposition).

  set (h ++
      [StringLang.Instr instr_label (StringLang.APPEND 0 (Z (max_z_nat + 2)))] ++
      (get_if_macro_label x (Some (A (max_label_nat + StringUtils.get_max_label h + 1))) max_char
      (max_label_nat + StringUtils.get_max_label h + 1 + 1) ++
      [StringLang.Instr None (StringLang.APPEND 0 (Z (max_z_nat + 1)))] ++
      [StringLang.Instr None
      (StringLang.IF_ENDS_GOTO (Z (max_z_nat + 2)) 0
      (A (max_label_nat + StringUtils.get_max_label h + 1 + 1 + max_char + 1 + 1 + max_char + 1)))] ++
      [StringLang.Instr (Some (A (max_label_nat + StringUtils.get_max_label h + 1 + 1 + max_char))) (StringLang.DEL x)] ++
      [StringLang.Instr None (StringLang.APPEND 0 (Z (max_z_nat + 1)))] ++
      [StringLang.Instr None (StringLang.IF_ENDS_GOTO (Z (max_z_nat + 2)) 0
      (A (max_label_nat + StringUtils.get_max_label h + 1)))] ++
      get_all_incr_blocks x (Z (max_z_nat + 1)) (Z (max_z_nat + 2)) max_char
      (max_label_nat + StringUtils.get_max_label h + 1 + 1)
      (A (max_label_nat + StringUtils.get_max_label h + 1 + 1 + max_char + 1)) ++
      transfer_block (A (max_label_nat + StringUtils.get_max_label h + 1 + 1 + max_char + 1)) x (Z (max_z_nat + 1))
      (max_label_nat + StringUtils.get_max_label h + 1 + 1 + max_char + 1 + 1)
      (A (max_label_nat + StringUtils.get_max_label h + 1 + 1 + max_char + 1 + 1 + max_char + 1)) (Z (max_z_nat + 2))
      max_char)) as h'.

  set ([StringLang.Instr
(Some
(A
(max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 +
max_char + 1 + 1 + max_char + 1))) 
(StringLang.DEL (Z (max_z_nat + 2)))] ++ [] ++ t) as t'.

  (* 3. Usando Lema para executar transferência de Z 
        para X *)
  pose proof (TransferMacroProperties.compute_transfer_block
  max_char p_str n s
  (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 +
  max_char + 1) (Z (max_z_nat + 1)) x
  (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 +
  max_char + 1 + 1 + max_char + 1))
  (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 +
  max_char + 1 + 1) h' t' (Z (max_z_nat + 2)) (s (Z (max_z_nat + 1)))) as 
  H_transfer. unfold max_label_str in *.

  destruct H_transfer as [transfer_steps H_transfer]; auto.
  rewrite p_str_decomposition. unfold h', t'. aac_reflexivity.
  unfold h'. repeat (solve_less_than_app).
  unfold h'. repeat (solve_less_than_app).
  lia.
  unfold h'. rewrite Hn, p_str_decomposition.
  repeat (rewrite <- app_assoc).
  repeat(rewrite_labeled_instr_app).
  replace ((max_label_nat + StringUtils.get_max_label h + 
  1 + 1 + max_char + 1 + 1 + max_char + 1)) with 
  (max_label_nat + StringUtils.get_max_label h + max_char + 
  max_char + 5) by lia.
  rewrite get_labeled_instr_transfer.
  repeat (rewrite length_app). lia.
  unfold StringLang.state_over. intros x0.
  destruct (triple_dec x0 x (Z (max_z_nat + 1))).
  rewrite H, Hsx. reflexivity. destruct H.
  rewrite H, Hsz1, Heqone_step_state. 
  StringLang.solve_string. lia.
  apply incr_string_over. StringLang.solve_string. lia.
  replace (s x0) with (one_step_state x0).
  rewrite Heqone_step_state. StringLang.solve_string; lia.
  symmetry. apply Hsforall. destruct H; auto.
  replace ((s (Z (max_z_nat + 2)))) 
  with (one_step_state (Z (max_z_nat + 2))).
  rewrite Heqone_step_state.
  solve_var_equation. rewrite H_aux_value. reflexivity.
  symmetry. apply Hsforall. split.
  rewrite var_eqb_neq in *. auto. injection. lia.
  rewrite var_eqb_neq in *. auto. simpl.
  rewrite PeanoNat.Nat.eqb_neq. lia.

  exists transfer_steps.
  destruct ((StringLang.compute_program p_str 
  (StringLang.SNAP n s) transfer_steps)) as [tr_line tr_state].
  simpl in H_transfer. 
  destruct H_transfer as [Htrline [Htrz1 [Htrx Htrforall]]].
  rewrite Htrline. exists 1. rewrite p_str_decomposition.
  simpl. repeat (progress_step).
  assert (eqb_opt_lbl instr_label (Some (A (max_label_nat + (StringUtils.get_max_label h 
  + S (S (max_char + S (S (max_char + S (S (max_char + 1)))))))))) = false) as 
  eqb_instr_false.

  {destruct instr_label; auto. destruct l. simpl.
  simpl in  label_lt_max_nat. rewrite PeanoNat.Nat.eqb_neq.
  lia. } simpl. rewrite eqb_instr_false.
  repeat (progress_step).
  repeat (split; auto).
  + unfold macro_length. rewrite <- macros_same_size with
    (max_lbl_nat := max_label_nat) (max_z_nat := max_z_nat) 
    (max_label_str := max_label_str). unfold max_label_str.
    simpl.
    repeat (rewrite <- app_assoc). 
    repeat (simpl; rewrite length_app). 
    (* lia falha *)
    repeat (rewrite <- PeanoNat.Nat.add_assoc).
    reflexivity.
  + solve_var_equation. rewrite Htrx, Hsx, Hsz1, Heqone_step_state.
    simpl. solve_var_equation. simpl. 
    replace (Nat.eqb (max_z_nat + 2) (max_z_nat + 1)) with false.
    reflexivity. symmetry. rewrite PeanoNat.Nat.eqb_neq. lia.
  + solve_var_equation. rewrite Htrz1.
    replace (eqb_var (Z (max_z_nat + 2)) (Z (max_z_nat + 1))) with false.
    reflexivity. symmetry. simpl. rewrite PeanoNat.Nat.eqb_neq; lia.
  + intros var [var_diff_x var_diff_z]. solve_var_equation.
    destruct (var_eqb_dec var (Z (max_z_nat + 2))).
    ++ rewrite e, eqb_var_refl. replace (tr_state (Z (max_z_nat + 2)))
       with (one_step_state (Z (max_z_nat + 2))). rewrite Heqone_step_state.
       solve_var_equation. simpl. rewrite H_aux_value; reflexivity.
       symmetry. transitivity (s var). rewrite e.  apply Htrforall.
       split. injection; lia. symmetry. rewrite <- var_eqb_neq; auto.
       rewrite e. apply Hsforall. split. symmetry. 
       rewrite <- var_eqb_neq; auto. injection; lia.
    ++ replace (eqb_var (Z (max_z_nat + 2)) var) with false.
       transitivity (s var). auto. transitivity (one_step_state var).
       auto. rewrite Heqone_step_state. solve_var_equation.
       rewrite <- var_eqb_neq in n0. rewrite eqb_var_symm, n0.
       reflexivity. symmetry. rewrite var_eqb_neq. auto.
Qed.

Print Assumptions compute_incr_macro.
