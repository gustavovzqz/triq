From Triq Require StringLang.
From Triq Require Import LanguagesCommon.
From Triq Require Import LanguagesUtils.
From Triq Require StringUtils.
From Triq Require Import StringMacros.
From Triq Require TransferMacroProperties.


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
    rewrite nth_error_app2 by lia. rewrite PeanoNat.Nat.sub_diag.
    simpl. rewrite H_x_value. simpl. rewrite char_eq_0, PeanoNat.Nat.eqb_refl.
    simpl. rewrite StringUtils.get_labeled_instr_app.
    rewrite nth_error_app2 by lia. rewrite cancel_sub. simpl.
    assert (Nat.eqb label_idx if_goto_idx = false) as label_diff_goto.
    {rewrite PeanoNat.Nat.eqb_neq. lia. } rewrite label_diff_goto.
    simpl. rewrite StringUtils.get_labeled_instr_app.
    rewrite nth_error_app2 by lia. rewrite cancel_sub.
    simpl. replace (if_goto_idx + 0) with (if_goto_idx) by lia.
    rewrite PeanoNat.Nat.eqb_refl. simpl.
    rewrite nth_error_app2 by lia. 
    replace (length h + S (length skip_block + 0) + 1 - length h)
    with (S (length skip_block) + 1) by lia. simpl.
    rewrite nth_error_app2 by lia. rewrite cancel_sub.
    simpl. rewrite nth_error_app2 by lia.
    replace (length h + S (length skip_block + 0) + 1 + 1 - length h)
    with (S (length skip_block) + 2) by lia. simpl.
    rewrite nth_error_app2 by lia. rewrite cancel_sub.
    simpl. assert (StringLang.ends_with
    (StringLang.append 1 (StringLang.del state_str x) z aux) 0 = true)
    as ends_with_steps_true.
    { unfold StringLang.append, StringLang.del, StringLang.update.
      rewrite z_diff_aux, x_diff_aux, ends_with_aux. reflexivity. }
    rewrite ends_with_steps_true.
    simpl. repeat (split; auto).
    ++ unfold StringLang.append, StringLang.del, StringLang.update.
       rewrite eqb_var_symm, x_diff_z, eqb_var_refl, H_x_value.
       reflexivity.
    ++ unfold StringLang.append, StringLang.del, StringLang.update.
       rewrite eqb_var_refl, x_diff_z. reflexivity.
    ++ intros var [var_diff_x var_diff_z]. rewrite <- var_eqb_neq in *.
       unfold StringLang.append, StringLang.del, StringLang.update.
       rewrite eqb_var_symm, var_diff_z. rewrite eqb_var_symm, var_diff_x.
       reflexivity.
    ++ apply StringUtils.labels_greater_implies_diff with if_goto_idx; auto.
    ++ apply StringUtils.labels_less_implies_diff with if_goto_idx; auto.
  + assert (char = S max_char \/ char <> S max_char) as char_cases by lia.
    destruct char_cases as [char_eq_S | char_diff_S].
    ++ exists 4. rewrite p_str_decomposition. rewrite <- H_length.
       simpl. rewrite nth_error_app2 by lia. rewrite PeanoNat.Nat.sub_diag.
       simpl. rewrite H_x_value, char_eq_S. simpl. 
       rewrite PeanoNat.Nat.eqb_refl. simpl.
       rewrite StringUtils.get_labeled_instr_app.
       rewrite nth_error_app2 by lia. rewrite cancel_sub.
       simpl.
       assert (Nat.eqb label_idx (S (max_char + if_goto_idx)) = false)
       as eqb_false_char. 
       {rewrite PeanoNat.Nat.eqb_neq; lia. } rewrite eqb_false_char. simpl.
       rewrite StringUtils.get_labeled_instr_app.
       rewrite nth_error_app2 by lia. rewrite cancel_sub.
       rewrite StringUtils.get_labeled_instr_app.
       rewrite nth_error_app2 by lia. rewrite cancel_sub.
       simpl. assert (Nat.eqb (if_goto_idx + S max_char)
       (S (max_char + if_goto_idx)) = true). 
       { rewrite PeanoNat.Nat.eqb_eq; lia. }
       rewrite H. simpl. rewrite nth_error_app2 by lia.
       replace (length h + S (length (get_if_macro_label x 
       (Some (A label_idx)) max_char if_goto_idx) + (length skip_block + 0)) + 1 - length h)
       with (S (length (get_if_macro_label x (Some (A label_idx)) max_char if_goto_idx) + 
       (length skip_block) + 1)) by lia. simpl.
       rewrite nth_error_app2 by lia.
       replace (_ + _ + 1 - _) with (length skip_block + 1) by lia.
       rewrite nth_error_app2 by lia. rewrite cancel_sub.
       simpl. rewrite nth_error_app2 by lia.
       replace (length h + S (length (get_if_macro_label x (Some (A label_idx)) max_char 
       if_goto_idx) + (length skip_block + 0)) + 1 + 1 - length h) 
       with (S (length (get_if_macro_label x (Some (A label_idx)) max_char if_goto_idx) + 
       length skip_block + 2)) by lia. simpl. rewrite nth_error_app2 by lia.
       rewrite nth_error_app2 by lia. 
       replace (_ + _ + 2 - _ - _) with 2 by lia.
       simpl. assert (StringLang.ends_with (StringLang.append 
       (S (max_char + 1)) (StringLang.del state_str x) z aux) 0 = true).
       { unfold StringLang.append, StringLang.del, StringLang.update.
         rewrite z_diff_aux, x_diff_aux. auto. }
       rewrite H0. simpl. repeat (split; auto).
       * unfold StringLang.append, StringLang.del, StringLang.update.
         rewrite eqb_var_symm, x_diff_z, eqb_var_refl, H_x_value.
         reflexivity.
       * unfold StringLang.append, StringLang.del, StringLang.update.
         rewrite eqb_var_refl, x_diff_z. reflexivity.
       * intros var [var_diff_x var_diff_z].
         unfold StringLang.append, StringLang.del, StringLang.update.
         rewrite <- var_eqb_neq in *. rewrite eqb_var_symm in var_diff_x,
         var_diff_z. rewrite var_diff_z, var_diff_x. reflexivity.
       * apply StringUtils.labels_greater_implies_diff with 
         (S max_char + if_goto_idx); auto.
       * apply labeled_instr_if_macro_false. lia.
       * replace (S (max_char + if_goto_idx)) with (S max_char + if_goto_idx)
         by lia. apply StringUtils.labels_less_implies_diff with 
         if_goto_idx; auto. lia.
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
       rewrite <- H_length.
       exists 1. rewrite p_str_decomposition. simpl.
       rewrite nth_error_app2 by lia. rewrite PeanoNat.Nat.sub_diag.
       simpl. assert (StringLang.ends_with (state_str x) 
       (S max_char) = false). 
       { rewrite H_x_value. simpl. rewrite PeanoNat.Nat.eqb_neq. lia.  } 
       rewrite H. 
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
          x z label_idx goto_label if_goto_idx h t aux char s,

  p_str = h ++
  get_if_macro_label x (Some (A (label_idx))) max_char if_goto_idx ++ 
  ([StringLang.Instr None (StringLang.APPEND 0 z)] ++ 
  [StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 goto_label)]) ++

  [StringLang.Instr (Some (A (if_goto_idx + max_char))) (StringLang.DEL x)] ++
   [StringLang.Instr None (StringLang.APPEND 0 z)] ++
   [StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 (A label_idx))] ++

  get_all_incr_blocks x z aux max_char if_goto_idx goto_label ++ t ->

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
    (line_str = StringLang.get_labeled_instr p_str goto_label /\
     state_str' x = s /\
     state_str' z = (state_str z) ++ [char + 1])) 
  /\
  forall var, 
  (var <> x /\ var <> z) ->
  state_str' var = state_str var.
Proof.
  destruct max_char; intros p_str pos_str state_str x z label_idx goto_label
  if_goto_idx h t aux char s;
  intros p_str_decomposition less_than_H H_length H_x_value label_le 
  char_leq_max ends_with_aux x_diff_z x_diff_aux z_diff_aux.
  - assert (char = 0) as char_eq_0 by lia. 
    rewrite char_eq_0, PeanoNat.Nat.eqb_refl.
    simpl in p_str_decomposition. replace (if_goto_idx + 0) with if_goto_idx
    in p_str_decomposition by lia. rewrite p_str_decomposition.
    exists 4. simpl. rewrite <- H_length. rewrite nth_error_app2 by lia.
    rewrite PeanoNat.Nat.sub_diag. simpl. rewrite H_x_value. simpl.
    rewrite char_eq_0. rewrite PeanoNat.Nat.eqb_refl. simpl.
    rewrite StringUtils.get_labeled_instr_app.
    rewrite nth_error_app2 by lia. rewrite cancel_sub.
    simpl. assert (Nat.eqb label_idx if_goto_idx = false) as label_diff_goto.
    {rewrite PeanoNat.Nat.eqb_neq. lia. } rewrite label_diff_goto,
    PeanoNat.Nat.eqb_refl. simpl. rewrite nth_error_app2 by lia.
    replace (length h + 3 + 1 - length h) with 4 by lia.
    simpl. rewrite nth_error_app2 by lia. 
    replace (length h + 3 + 1 + 1 - length h) with 5 by lia. simpl.
    assert (StringLang.ends_with  (StringLang.append 0 
    (StringLang.del state_str x) z aux) 0 = true) as ends_with_true.
    { unfold StringLang.append, StringLang.del, StringLang.update.
      rewrite z_diff_aux, x_diff_aux, ends_with_aux. reflexivity. }
    rewrite ends_with_true. simpl. repeat (split; auto).
    + unfold StringLang.append, StringLang.del, StringLang.update.
      rewrite eqb_var_symm, x_diff_z, eqb_var_refl, H_x_value.
      reflexivity.
    + unfold StringLang.append, StringLang.del, StringLang.update.
      rewrite eqb_var_refl, x_diff_z. reflexivity.
    + intros var [var_diff_x var_diff_z].
      unfold StringLang.append, StringLang.del, StringLang.update.
      rewrite <- var_eqb_neq in var_diff_x, var_diff_z.
      rewrite eqb_var_symm in var_diff_x, var_diff_z.
      rewrite var_diff_z, var_diff_x. reflexivity.
    + apply StringUtils.labels_less_implies_diff with (if_goto_idx);
      auto.
  - simpl. assert (char = S max_char \/ char <> S max_char) as 
    char_cases by lia.
    destruct char_cases as [char_eq_S | char_diff_S].
    + rewrite char_eq_S, PeanoNat.Nat.eqb_refl.
      exists 4. rewrite p_str_decomposition. rewrite <- H_length. 
      simpl. rewrite nth_error_app2 by lia. rewrite PeanoNat.Nat.sub_diag.
      simpl. rewrite H_x_value, char_eq_S. simpl.
      rewrite PeanoNat.Nat.eqb_refl. simpl. 
      rewrite StringUtils.get_labeled_instr_app. 
      rewrite nth_error_app2 by lia. rewrite cancel_sub.
      simpl. assert (Nat.eqb label_idx (S (max_char + if_goto_idx)) = false)
      as label_diff_S_max. { rewrite PeanoNat.Nat.eqb_neq. lia. }
      rewrite label_diff_S_max. simpl. 
      rewrite StringUtils.get_labeled_instr_app. 
      rewrite nth_error_app2 by lia. rewrite cancel_sub.
      simpl. replace (S (max_char + if_goto_idx)) with 
      (if_goto_idx + S max_char ) by lia. rewrite PeanoNat.Nat.eqb_refl.
      simpl. rewrite nth_error_app2 by lia.
      replace (length h + S (length (get_if_macro_label x (Some (A label_idx)) 
      max_char if_goto_idx) + 2) + 1 - length h) with (S (length 
      (get_if_macro_label x (Some (A label_idx)) max_char if_goto_idx) + 3))
      by lia. simpl. rewrite nth_error_app2 by lia. rewrite cancel_sub.
      simpl. rewrite nth_error_app2 by lia.
      replace ((length h + S (length (get_if_macro_label x 
      (Some (A label_idx)) max_char if_goto_idx) + 2) + 1 + 1 - length h))
      with (S (length (get_if_macro_label x (Some (A label_idx)) 
      max_char if_goto_idx)) + 4) by lia. simpl.
      rewrite nth_error_app2 by lia. rewrite cancel_sub. simpl.
      assert (StringLang.ends_with (StringLang.append 0 (StringLang.del 
      state_str x) z aux) 0 = true) as ends_with_true.
      { unfold StringLang.append, StringLang.del, StringLang.update. 
        rewrite z_diff_aux, x_diff_aux, ends_with_aux. reflexivity. }
      rewrite ends_with_true. repeat (split; auto).
      ++ unfold StringLang.append, StringLang.del, StringLang.update.
         rewrite eqb_var_symm, x_diff_z, eqb_var_refl, H_x_value.
         reflexivity.
      ++ unfold StringLang.append, StringLang.del, StringLang.update.
         rewrite eqb_var_refl, x_diff_z. reflexivity.
      ++ intros var [var_diff_x var_diff_z].
         unfold StringLang.append, StringLang.del, StringLang.update.
         rewrite <- var_eqb_neq in var_diff_x, var_diff_z.
         rewrite eqb_var_symm in var_diff_x, var_diff_z.
         rewrite var_diff_z, var_diff_x. reflexivity.
      ++ apply labeled_instr_if_macro_false. lia.
      ++ apply StringUtils.labels_less_implies_diff with (if_goto_idx);
         auto. lia.
    + assert (PeanoNat.Nat.eqb char (S max_char) = false).
      { rewrite PeanoNat.Nat.eqb_neq. lia. } rewrite H.
      cut (exists n n' : nat, 
      let (line_str, state_str') := StringLang.split_snap
      (StringLang.compute_program p_str (StringLang.compute_program p_str 
      (StringLang.SNAP pos_str state_str) n) n') 
      in (line_str = StringLang.get_labeled_instr p_str goto_label /\
      state_str' x = s /\ state_str' z = state_str z ++ [char + 1]) /\
      (forall var : variable,
      var <> x /\ var <> z -> state_str' var = state_str var)).
      {intros cH. destruct cH as [m [m']]. exists (m' + m). 
       rewrite StringLangProperties.compute_program_add. auto. }
      simpl in p_str_decomposition.

      rewrite p_str_decomposition. simpl.
      exists 1. rewrite <- H_length. simpl. 
      rewrite nth_error_app2 by lia. rewrite PeanoNat.Nat.sub_diag.
      assert (StringLang.ends_with (state_str x) (S max_char) = false).
      { rewrite H_x_value. simpl. auto. } simpl. rewrite H0. 
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
      x z aux max_char if_goto_idx goto_label ++ t) as p_str_eq.
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




Lemma compute_char_transfer' :
  forall max_char p_str pos_str state_str 
         label_idx x z goto_label if_goto_idx
         h t skip_block aux char s,

  p_str = h ++
  transfer_block (A label_idx) x z if_goto_idx goto_label aux max_char  ++
  t ->

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

  line_str = StringLang.get_labeled_instr p_str (A label_idx) /\
  state_str' x = s /\
  state_str' z =  (state_str z) ++ [char] /\
  forall var, 
  (var <> x /\ var <> z) ->
  state_str' var = state_str var.
Proof.
  intros. unfold transfer_block in *. rewrite H. apply TransferMacroProperties.compute_char_transfer
  with max_char goto_label if_goto_idx h t [] aux; eauto.
  aac_reflexivity. simpl. apply I.
Qed.


 Lemma compute_incr_macro :
  forall max_char p_str pos_str state_str 
         instr_label x 
         max_label_nat max_z_nat max_z_str h t x_value, 

  p_str = h ++
  StringMacros.get_str_macro 
  (NatLang.Instr instr_label (NatLang.INCR x)) 
  max_char max_label_nat max_z_nat
  max_z_str ++ t  ->

  length h = pos_str  ->


  state_str x = x_value ->
  state_str (Z (max_z_nat + 2)) = [0] ->

  exists n,
  let (line_str, state_str') :=
    StringLang.split_snap
      (StringLang.compute_program p_str (StringLang.SNAP (pos_str + 1) state_str)
         n) in

  line_str = pos_str + StringMacros.macro_length 
  (NatLang.Instr instr_label (NatLang.INCR x)) max_char /\  
  state_str' x = incr_string (state_str x) max_char /\
  state_str' (Z (max_z_nat + 2)) = [] /\
  forall var, 
  var <> x /\ var <> (Z (max_z_nat + 2)) ->
  state_str' var = state_str var.
Proof.
  intros max_char p_str pos_str state_str instr_label x 
  max_label_nat max_z_nat max_z_str h t x_value.
  intros p_str_decomposition H_length H_x_value H_aux_value.


  (* Indução em x_value *)

  generalize dependent state_str. induction x_value ; 
  intros state_str H_x_value H_aux_value.
  - cut (exists n n' : nat, 
    let (line_str, state_str') := StringLang.split_snap
    (StringLang.compute_program p_str (StringLang.compute_program p_str 
    (StringLang.SNAP (pos_str + 1) state_str) n) n') in 

    line_str = pos_str + macro_length (NatLang.Instr instr_label (NatLang.INCR x))
    max_char /\
    state_str' x = incr_string (state_str x) max_char /\
    state_str' (Z (max_z_nat + 2)) = [] /\
    (forall var : variable,
    var <> x /\ var <> Z (max_z_nat + 2) -> state_str' var = state_str var)).
    {intros cH. destruct cH as [m [m']]. exists (m' + m). 
       rewrite StringLangProperties.compute_program_add. auto. }
    unfold get_str_macro in p_str_decomposition.
    unfold get_incr_macro in p_str_decomposition.
    set ([StringLang.Instr None (StringLang.APPEND 0 (Z (max_z_nat + 1)))] ++
        [StringLang.Instr None
        (StringLang.IF_ENDS_GOTO (Z (max_z_nat + 2)) 0
        (A (max_label_nat + max_z_str + 1 + 1 + max_char + 1 + 1 + max_char + 1 + max_char + 1)))] ++
        [StringLang.Instr (Some (A (max_label_nat + max_z_str + 1 + 1 + max_char))) (StringLang.DEL x)] ++
        [StringLang.Instr None (StringLang.APPEND 0 (Z (max_z_nat + 1)))] ++
        [StringLang.Instr None (StringLang.IF_ENDS_GOTO (Z (max_z_nat + 2)) 0 (A (max_label_nat + max_z_str + 1)))] ++
        get_all_incr_blocks x (Z (max_z_nat + 1)) (Z (max_z_nat + 2)) max_char (max_label_nat + max_z_str + 1)
        (A (max_label_nat + max_z_str + 1 + 1 + max_char + 1)) ++
        transfer_block (A (max_label_nat + max_z_str + 1 + 1 + max_char + 1)) x (Z (max_z_nat + 1))
        (max_label_nat + max_z_str + 1 + 1 + max_char + 1 + 1)
        (A (max_label_nat + max_z_str + 1 + 1 + max_char + 1 + 1 + max_char + 1 + max_char + 1)) (Z (max_z_nat + 2)) max_char ++
        transfer_block (A (max_label_nat + max_z_str + 1 + 1 + max_char + 1 + 1 + max_char + 1)) (Z (max_z_nat + 1)) x
        (max_label_nat + max_z_str + 1 + 1 + max_char + 1 + 1 + max_char + 1 + 1)
        (A (max_label_nat + max_z_str + 1 + 1 + max_char + 1 + 1 + max_char + 1 + max_char + 1)) (Z (max_z_nat + 2)) max_char ++
        [StringLang.Instr (Some (A (max_label_nat + max_z_str + 1 + 1 + max_char + 1 + 1 + max_char + 1 + max_char + 1)))
        (StringLang.DEL (Z (max_z_nat + 2)))] ++ t) as t'.


    set (h ++ [StringLang.Instr instr_label 
    (StringLang.APPEND 0 (Z (max_z_nat + 2)))]) as h'.
    pose proof (IfMacroProperties.compute_if_block_label_skip max_char p_str (pos_str + 1)
    state_str x (Some (A (max_label_nat + max_z_str + 1))) 
    (max_label_nat + max_z_str + 1 + 1) h' t' )  as if_skip.
    destruct if_skip as [if_skip_steps H_if_skip]; auto.
    rewrite p_str_decomposition. unfold h', t'. aac_reflexivity.
    unfold h'. rewrite length_app, H_length. simpl. reflexivity. 
    clear t'. clear h'.
    exists if_skip_steps. destruct (StringLang.compute_program p_str 
    (StringLang.SNAP (pos_str + 1) state_str) if_skip_steps).
    simpl in H_if_skip. destruct H_if_skip as [s_eq n_eq].
    rewrite s_eq. rewrite n_eq.
    cut (exists n n' : nat, 
    let (line_str, state_str') := StringLang.split_snap
    (StringLang.compute_program p_str (StringLang.compute_program p_str 
    (StringLang.SNAP (pos_str + 1 + length (get_if_macro_label x 
    (Some (A (max_label_nat + max_z_str + 1))) max_char 
    (max_label_nat + max_z_str + 1 + 1))) state_str) n) n') in 

    line_str = pos_str + macro_length (NatLang.Instr instr_label (NatLang.INCR x))
    max_char /\
    state_str' x = incr_string (state_str x) max_char /\
    state_str' (Z (max_z_nat + 2)) = [] /\
    (forall var : variable,
    var <> x /\ var <> Z (max_z_nat + 2) -> state_str' var = state_str var)).
    {intros cH. destruct cH as [m [m']]. exists (m' + m). 
       rewrite StringLangProperties.compute_program_add. auto. }

  exists 2. rewrite <- H_length. simpl. rewrite p_str_decomposition.
  rewrite nth_error_app2 by lia.
  replace (length h + 1 + length (get_if_macro_label x 
  (Some (A (max_label_nat + max_z_str + 1))) max_char 
  (max_label_nat + max_z_str + 1 + 1)) - length h) with (1 + 
  length (get_if_macro_label x (Some (A (max_label_nat + max_z_str + 1))) max_char 
  (max_label_nat + max_z_str + 1 + 1))) by lia.

  simpl. rewrite <- app_assoc. rewrite nth_error_app2 by lia.
  rewrite PeanoNat.Nat.sub_diag. simpl.
  Set Printing Parentheses.
  repeat (rewrite (PeanoNat.Nat.add_assoc)).
  

  rewrite nth_error_app2 by lia.
  cancel_nat_outer.
simpl. rewrite nth_error_app2 by lia. cancel_nat_outer.
simpl. assert (StringLang.ends_with
(StringLang.append 0 state_str (Z (max_z_nat + 1)) (Z (max_z_nat + 2)))
0 = true ) as ends_with_true. { admit. } rewrite ends_with_true.
simpl. rewrite StringUtils.get_labeled_instr_app; simpl.
rewrite StringUtils.get_labeled_instr_app; simpl.
rewrite <- app_assoc.
rewrite StringUtils.get_labeled_instr_app; simpl.
rewrite <- app_assoc.
rewrite StringUtils.get_labeled_instr_app; simpl.
Admitted.




  
    