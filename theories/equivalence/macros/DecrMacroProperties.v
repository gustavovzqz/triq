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

Lemma compute_char_decr_S :
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
  induction max_char;
  intros p_str pos_str state_str label_idx x z if_goto_idx h t goto_label
    skip_block aux char s;
  intros p_str_decomposition label_ge_skip labels_lt_h label_lt_goto
    H_length H_x_value char_le_max char_gt_0 ends_with_aux x_diff_z x_diff_aux z_diff_aux.
  + exfalso. lia.
  + assert (char = S max_char \/ char <> S max_char) as char_cases by lia.
    destruct char_cases as [char_eq_S | char_diff_S].
    * exists 4. rewrite p_str_decomposition. rewrite <- H_length.
      repeat (progress_step).
      rewrite H_x_value. simpl. rewrite char_eq_S, PeanoNat.Nat.eqb_refl.
      repeat (progress_step).
      assert (StringLang.ends_with (StringLang.append (max_char - 0)
        (StringLang.del state_str x) z aux) 0 = true) as ends_with_true.
      { unfold StringLang.append, StringLang.del, StringLang.update.
        rewrite z_diff_aux, x_diff_aux, ends_with_aux. reflexivity. }
      rewrite ends_with_true. simpl. repeat (split; auto); solve_var_equation.
      ++ rewrite H_x_value. reflexivity.
      ++ intros var [var_diff_x var_diff_z]. rewrite <- var_eqb_neq in *.
         solve_var_equation.
    * cut (exists n n' : nat,
        let (line_str, state_str') := StringLang.split_snap
          (StringLang.compute_program p_str (StringLang.compute_program p_str
          (StringLang.SNAP pos_str state_str) n) n')
          in (line_str = StringLang.get_labeled_instr p_str goto_label /\
          state_str' x = s /\ state_str' z = state_str z ++ [char - 1]) /\
          (forall var : variable,
          var <> x /\ var <> z -> state_str' var = state_str var)).
      { intros cH. destruct cH as [m [m']]. exists (m' + m).
        rewrite StringLangProperties.compute_program_add. auto. }
      rewrite <- H_length. rewrite p_str_decomposition.
      exists 1. repeat (progress_step).
      assert (StringLang.ends_with (state_str x) (S max_char) = false) as ends_with_S.
      { rewrite H_x_value. simpl. rewrite PeanoNat.Nat.eqb_neq. lia. }
      rewrite ends_with_S.
      repeat (rewrite cons_app_assoc). rewrite app_assoc.
      remember (h ++ [StringLang.Instr (Some (A label_idx))
        (StringLang.IF_ENDS_GOTO x (S max_char) (A (S (max_char + if_goto_idx))))]) as h'.
      set (skip_block ++ [StringLang.Instr (Some (A (if_goto_idx + S max_char))) (StringLang.DEL x)] ++
        [StringLang.Instr None (StringLang.APPEND (S max_char - 1) z)] ++
        [StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 goto_label)]) as skip_block'.
      apply IHmax_char with label_idx if_goto_idx h' t skip_block' aux; auto.
      ++ unfold skip_block'. simpl. repeat (rewrite cons_app_assoc).
         repeat (rewrite <- app_assoc). simpl. reflexivity.
      ++ unfold skip_block'. apply StringUtils.labels_greater_than_app.
         ** apply StringUtils.labels_greater_than_S.
            replace (S (max_char + if_goto_idx)) with (S max_char + if_goto_idx) by lia. auto.
         ** simpl. lia.
      ++ rewrite Heqh'. apply StringUtils.labels_less_than_app; auto.
         simpl; lia.
      ++ rewrite Heqh'. rewrite length_app. reflexivity.
      ++ lia.
Qed.


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

  StringLang.string_over (char :: s) max_char ->

  StringLang.ends_with (state_str aux) 0 = true ->


  eqb_var x z = false ->
  eqb_var x aux = false ->
  eqb_var z aux = false ->


  exists n,

  let (line_str, state_str') :=
    StringLang.split_snap (StringLang.compute_program p_str
    (StringLang.SNAP pos_str state_str) n) in
  (
  (char = 0 /\ s = [] /\
    line_str = StringLang.get_labeled_instr p_str T2 /\
    state_str' x = [] /\
    state_str' z = state_str z)
  \/
  (char = 0 /\ s <> [] /\
    line_str = StringLang.get_labeled_instr p_str (A label_idx) /\
    state_str' x = s /\
    state_str' z = state_str z ++ [max_char])
  \/
  (char > 0 /\
    line_str = StringLang.get_labeled_instr p_str T1 /\
    state_str' x = s /\
    state_str' z = (state_str z) ++ [char - 1])
  )
  /\
  (forall var, (var <> x /\ var <> z) ->
    state_str' var = state_str var).
Proof.
  intros max_char p_str pos_str state_str x z label_idx if_goto_idx 
  h t aux char s T1 T2.
  intros p_str_decomposition labels_h_lt_if_goto length_eq x_value 
  label_idx_lt_goto_idx string_over_value ends_with_aux x_diff_z
  x_diff_aux z_diff_aux.
  destruct char as [| char' ].
  (* Caso 1 - char = 0 *)
  - (* Pulando parte inicial do IF *)
      cut (exists n n' : nat,
        let (line_str, state_str') := StringLang.split_snap
          (StringLang.compute_program p_str
            (StringLang.compute_program p_str
              (StringLang.SNAP pos_str state_str) n) n') in
        ((0 = 0 /\ s = [] /\
            line_str = StringLang.get_labeled_instr p_str T2 /\
            state_str' x = [] /\ state_str' z = state_str z) \/
        (0 = 0 /\ s <> [] /\
            line_str = StringLang.get_labeled_instr p_str (A label_idx) /\
            state_str' x = s /\ state_str' z = state_str z ++ [max_char]) \/
        (0 > 0 /\
            line_str = StringLang.get_labeled_instr p_str T1 /\
            state_str' x = s /\ state_str' z = state_str z ++ [0 - 1]))
        /\
        forall var : variable, var <> x /\ var <> z ->
          state_str' var = state_str var).
      { intros cH. destruct cH as [m [m']]. exists (m' + m).
        rewrite StringLangProperties.compute_program_add. auto. }
    assert (exists n, let (line_str, state_str') :=
    StringLang.split_snap (StringLang.compute_program p_str 
    (StringLang.SNAP pos_str state_str) n) in
    state_str' = state_str /\ line_str = 
    StringLang.get_labeled_instr p_str (A (0 + if_goto_idx))) as if_computation.
    { remember ([StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 T2)] ++
      get_all_ai_blocks_decr x z aux max_char if_goto_idx T1 ++
      [StringLang.Instr (Some (A if_goto_idx)) (StringLang.DEL x)] ++
      get_if_macro x None (A (if_goto_idx + max_char + 1)) max_char ++
      [StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 T2)] ++
      [StringLang.Instr (Some (A (if_goto_idx + max_char + 1)))
      (StringLang.APPEND max_char z)] ++
      [StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 (A label_idx))]
      ++ t) as t'.
      apply IfMacroProperties.compute_if_block_label_value with 
      (max_char := max_char) (x := x) (opt_label := (Some (A label_idx))) 
      (h := h) (t := t') (s := s); auto. lia.  }

      destruct if_computation as [if_steps H_if_computation].
      exists if_steps. 
      destruct (StringLang.compute_program p_str (StringLang.SNAP 
      pos_str state_str) if_steps) as [if_comp_line if_comp_state].
      simpl in H_if_computation. destruct H_if_computation as [H_if_state
      H_if_line]. rewrite H_if_state, H_if_line.
      (* Estou na linha da label [A1]
         executo 1 passo + if_steps + (depende)  *)
      cut (exists n n' : nat,
        let (line_str, state_str') := StringLang.split_snap
          (StringLang.compute_program p_str
            (StringLang.compute_program p_str
              (StringLang.SNAP (StringLang.get_labeled_instr p_str (A if_goto_idx))
                state_str) n) n') in
        ((0 = 0 /\ s = [] /\
            line_str = StringLang.get_labeled_instr p_str T2 /\
            state_str' x = [] /\ state_str' z = state_str z) \/
        (0 = 0 /\ s <> [] /\
            line_str = StringLang.get_labeled_instr p_str (A label_idx) /\
            state_str' x = s /\ state_str' z = state_str z ++ [max_char]) \/
        (0 > 0 /\
            line_str = StringLang.get_labeled_instr p_str T1 /\
            state_str' x = s /\ state_str' z = state_str z ++ [0 - 1]))
        /\
        forall var : variable, var <> x /\ var <> z ->
          state_str' var = state_str var).
      { intros cH. destruct cH as [m [m']]. exists (m' + m).
        rewrite StringLangProperties.compute_program_add. auto. }

      exists 1. simpl. rewrite p_str_decomposition.
      repeat (progress_step).

       remember (length h + (length (get_if_macro_label x 
         (Some (A label_idx)) max_char if_goto_idx) + S (length 
         (get_all_ai_blocks_decr x z aux max_char if_goto_idx T1) + 1))) 
         as pos_str'.



      (* Estamos no IF X != 0 GOTO C2 *)
      destruct s eqn:E.
      ++ (* Caso x = 0 -> Pulo o IF e executo o GOTO E*)
         assert (exists n, let (line_str, state_str') :=
         StringLang.split_snap (StringLang.compute_program p_str 
         (StringLang.SNAP pos_str' (StringLang.del state_str x)) n) in
         state_str' = (StringLang.del state_str x) /\ line_str = pos_str' +
         (length (get_if_macro x None (A (if_goto_idx + max_char + 1)) max_char)) 
          ) as if_computation_mid.
        { remember (h ++ get_if_macro_label x (Some (A label_idx)) max_char if_goto_idx ++
          [StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 T2)] ++
          get_all_ai_blocks_decr x z aux max_char if_goto_idx T1 ++
          [StringLang.Instr (Some (A if_goto_idx)) (StringLang.DEL x)]) as h'.

          remember ([StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 T2)] ++
          [StringLang.Instr (Some (A (if_goto_idx + max_char + 1))) (StringLang.APPEND max_char z)] ++
          [StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 (A label_idx))] ++ t) 
          as t'.
          apply IfMacroProperties.compute_if_block_skip with 
          (max_char := max_char) (opt_label := None) (x := x) (h := h') (t := t'). 
          rewrite p_str_decomposition, Heqh', Heqt'. aac_reflexivity.
          rewrite Heqpos_str', Heqh'. repeat (rewrite length_app).
          f_equal. solve_var_equation. rewrite x_value. reflexivity. }

        destruct if_computation_mid as [if_steps_mid H_if].
        exists (1 + if_steps_mid). rewrite StringLangProperties.compute_program_add.
        repeat (rewrite (cons_app_assoc)).
        replace (h ++ _ ) with p_str.
        (* preciso rewrite pstr etc pro destruct funcionar *)
        destruct ((StringLang.compute_program p_str 
        (StringLang.SNAP pos_str' (StringLang.del state_str x)) if_steps_mid))
        as [mid_if_line mid_if_state]. 
        destruct H_if as [H_mid_state H_mid_line]. rewrite H_mid_state, H_mid_line.
        rewrite Heqpos_str'. rewrite p_str_decomposition.
        repeat (progress_step).
        replace (StringLang.ends_with (StringLang.del state_str x aux) 0) with true.
        repeat (progress_step).
        split.
        left. repeat (split; auto; solve_var_equation).
        + rewrite x_value. reflexivity.
        + intros var [var_diff_x var_diff_z]. solve_var_equation.
          replace (eqb_var x var) with false. reflexivity. 
          symmetry. rewrite var_eqb_neq. auto.
        + solve_var_equation.
        + rewrite p_str_decomposition. rewrite PeanoNat.Nat.add_assoc.
          reflexivity.
       (* caso x != 0 *)
    ++ assert (exists n, let (line_str, state_str') :=
         StringLang.split_snap (StringLang.compute_program p_str 
         (StringLang.SNAP pos_str' (StringLang.del state_str x)) n) in
         state_str' = (StringLang.del state_str x) /\  line_str = 
         StringLang.get_labeled_instr p_str ((A (if_goto_idx + max_char + 1)))).
        { remember (h ++ get_if_macro_label x (Some (A label_idx)) max_char if_goto_idx ++
          [StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 T2)] ++
          get_all_ai_blocks_decr x z aux max_char if_goto_idx T1 ++
          [StringLang.Instr (Some (A if_goto_idx)) (StringLang.DEL x)]) as h'.

          remember ([StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 T2)] ++
          [StringLang.Instr (Some (A (if_goto_idx + max_char + 1))) (StringLang.APPEND max_char z)] ++
          [StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 (A label_idx))] ++ t) 
          as t'.
          apply IfMacroProperties.compute_if_block_Sn with 
          (max_char := max_char) (opt_label := None) (x := x)
          (h := h') (t := t') (char := n).
          rewrite p_str_decomposition, Heqh', Heqt'. aac_reflexivity.
          rewrite Heqpos_str', Heqh'. repeat (rewrite length_app).
          f_equal. simpl in string_over_value.  lia. solve_var_equation. 
          rewrite x_value. simpl. rewrite PeanoNat.Nat.eqb_refl. auto. }
        replace (h ++ _) with p_str.
        destruct H.
        cut (exists m m' : nat,
          let (line_str, state_str') :=
          StringLang.split_snap
          (StringLang.compute_program p_str
          (StringLang.compute_program p_str
          (StringLang.SNAP pos_str' (StringLang.del state_str x)) m) m') in
          ((0 = 0 /\ n :: l = [] /\
          line_str = StringLang.get_labeled_instr p_str T2 /\
          state_str' x = [] /\ state_str' z = state_str z) \/
          (0 = 0 /\ n :: l <> [] /\
          line_str = StringLang.get_labeled_instr p_str (A label_idx) /\
          state_str' x = n :: l /\ state_str' z = state_str z ++ [max_char]) \/
          (0 > 0 /\ line_str = StringLang.get_labeled_instr p_str T1 /\
          state_str' x = n :: l /\ state_str' z = state_str z ++ [0])) /\
          forall var : variable, var <> x /\ var <> z ->
            state_str' var = state_str var).
        { intros cH. destruct cH as [m [m']]. exists (m' + m).
          rewrite StringLangProperties.compute_program_add. auto. }
          exists x0. destruct ((StringLang.compute_program p_str
          (StringLang.SNAP pos_str' (StringLang.del state_str x)) x0)).
          destruct H. rewrite H0, H. exists 2.
          rewrite p_str_decomposition. repeat (progress_step).
          replace (StringLang.ends_with (StringLang.append max_char 
          (StringLang.del state_str x) z aux) 0) with true.
          repeat (split; auto).
          right. left. repeat (split; auto; solve_var_equation).
          + intros falso; discriminate.
          + rewrite x_value; reflexivity.
          + intros var [var_diff_x var_diff_z]. solve_var_equation.
            replace (eqb_var z var) with false.
            replace (eqb_var x var) with false. reflexivity.
            symmetry. rewrite var_eqb_neq. auto.
            symmetry. rewrite var_eqb_neq. auto.
          + solve_var_equation.
          + rewrite p_str_decomposition. repeat (rewrite cons_app_assoc).
            rewrite PeanoNat.Nat.add_assoc. reflexivity.
    (* char = S ... -> basta executar lema anterior*)
  - assert (exists n,
      let (line_str, state_str') := StringLang.split_snap
      (StringLang.compute_program p_str (StringLang.SNAP pos_str state_str) n) in
      (line_str = StringLang.get_labeled_instr p_str T1 /\
      state_str' x = s /\
      state_str' z =  (state_str z) ++ [(S char') - 1]) /\
      forall var, 
      (var <> x /\ var <> z) ->
      state_str' var = state_str var) as [char_steps H_char_comp ].
    { remember ([StringLang.Instr (Some (A if_goto_idx)) (StringLang.DEL x)] ++
      get_if_macro x None (A (if_goto_idx + max_char + 1)) max_char ++
      [StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 T2)] ++
      [StringLang.Instr (Some (A (if_goto_idx + max_char + 1)))
      (StringLang.APPEND max_char z)] ++
      [StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 (A label_idx))] ++ t)
      as t'. 
      remember ([StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 T2)]) as
      skip_block. 
      apply compute_char_decr_S with (max_char := max_char)
      (label_idx := label_idx) (if_goto_idx := if_goto_idx) (h := h)
      (t := t') (aux := aux) (skip_block := skip_block); auto; try lia.
      rewrite Heqskip_block. reflexivity. simpl in string_over_value. lia.  }
      exists char_steps. 
      destruct (StringLang.compute_program p_str (StringLang.SNAP pos_str 
      state_str) char_steps) as [line_char_comp state_char_comp].
      destruct H_char_comp as [[H_line_comp [H_state_comp_x H_state_comp_z ]] 
      h_forall_comp]. simpl. split; auto.
      right. right. repeat split; try lia; auto.
Qed.

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
  intros max_char p_str pos_str state_str instr_label x 
  max_label_nat max_z_nat h t x_value.
  intros max_label_str p_str_decomposition H_length label_lt_max_nat
  H_state_over string_over_x_value H_x_value H_aux_value 
  x_diff_aux x_diff_z.


  (* Indução em x_value *)

  generalize dependent state_str. induction x_value ; 
  intros state_str H_state_over H_x_value H_aux_value
  (* Caso x = [] -> pula o IF e cai no GOTO E *).
  - cut (exists n n' : nat, 
    let (line_str, state_str') := StringLang.split_snap
    (StringLang.compute_program p_str (StringLang.compute_program p_str 
    (StringLang.SNAP (pos_str + 1) state_str) n) n') in 
    line_str = StringLang.get_labeled_instr p_str
    (A (max_label_nat + max_label_str + max_char + max_char + 6)) /\
    state_str' x = [] /\
    state_str' (Z (max_z_nat + 1)) =
    state_str (Z (max_z_nat + 1)) ++ decr_string (state_str x) max_char /\
    (forall var : variable,
    var <> x /\ var <> Z (max_z_nat + 1) -> state_str' var =
    state_str var)).
    {intros cH. destruct cH as [m [m']]. exists (m' + m). 
       rewrite StringLangProperties.compute_program_add. auto. }
    unfold get_str_macro in p_str_decomposition.
    unfold get_decr_macro in p_str_decomposition.
    repeat (rewrite <- app_assoc in p_str_decomposition).
    assert (exists n, let (line_str, state_str') := StringLang.split_snap
    (StringLang.compute_program p_str (StringLang.SNAP (pos_str + 1) state_str) n) in
    state_str' = state_str /\
    line_str = (pos_str + 1)+ length (get_if_macro_label x (Some (A (max_label_nat + 
    max_label_str + 1))) max_char (max_label_nat + max_label_str + 1 + 1))) as skip_if.
    { remember (h ++ [StringLang.Instr instr_label (StringLang.APPEND 0 
      (Z (max_z_nat + 2)))]) as h'.
      remember ([StringLang.Instr None (StringLang.IF_ENDS_GOTO (Z (max_z_nat + 2)) 0 (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char +
      1)))] ++
      get_all_ai_blocks_decr x (Z (max_z_nat + 1)) (Z (max_z_nat + 2)) max_char (max_label_nat + max_label_str + 1 + 1)
      (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1)) ++
      [StringLang.Instr (Some (A (max_label_nat + max_label_str + 1 + 1))) (StringLang.DEL x)] ++
      get_if_macro x None (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1)) max_char ++
      [StringLang.Instr None (StringLang.IF_ENDS_GOTO (Z (max_z_nat + 2)) 0 (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char +
      1)))] ++
      [StringLang.Instr (Some (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1))) (StringLang.APPEND max_char (Z (max_z_nat + 1)))] ++
      [StringLang.Instr None (StringLang.IF_ENDS_GOTO (Z (max_z_nat + 2)) 0 (A (max_label_nat + max_label_str + 1)))] ++
      transfer_block (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1)) x (Z (max_z_nat + 1))
      (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1) (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char + 1))
      (Z (max_z_nat + 2)) max_char ++
      transfer_block (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char + 1)) (Z (max_z_nat + 1)) x
      (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char + 1 + 1)
      (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char + 1 + 1 + max_char + 1)) (Z (max_z_nat + 2)) max_char ++
      [StringLang.Instr (Some (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char + 1 + 1 + max_char + 1)))
      (StringLang.DEL (Z (max_z_nat + 2)))] ++ t) as t'.
      apply IfMacroProperties.compute_if_block_label_skip with (h := h') (t := t'); auto.
      rewrite p_str_decomposition, Heqh', Heqt'. aac_reflexivity.
      rewrite <- H_length, Heqh'. rewrite length_app. simpl. reflexivity. }
    destruct skip_if as [if_steps H_if]. exists if_steps.
    destruct (StringLang.compute_program p_str (StringLang.SNAP (pos_str + 1)
    state_str) if_steps) as [if_steps_line if_steps_state].
    destruct H_if as [H_if_skip_state H_if_skip_line].
    rewrite H_if_skip_state, H_if_skip_line. exists 1.
    rewrite <- H_length, p_str_decomposition.
    replace (max_label_nat + max_label_str + max_char + max_char + 6)  with (max_label_nat + (max_label_str + S (S (max_char + 
    S (S (S (max_char + 1))))))) by lia. 
    repeat (progress_step).
    rewrite H_aux_value. repeat split; auto.
    rewrite H_x_value. simpl. rewrite app_nil_r. reflexivity.

  - (* Dividindo em dois passos. *)
    cut (exists n n' : nat, 
    let (line_str, state_str') := StringLang.split_snap
    (StringLang.compute_program p_str (StringLang.compute_program p_str 
    (StringLang.SNAP (pos_str + 1) state_str) n) n') in 
     line_str = StringLang.get_labeled_instr p_str (A 
    (max_label_nat + max_label_str + max_char + max_char + 6)) /\  
    state_str' x = []  /\
    state_str' (Z (max_z_nat + 1)) = state_str (Z (max_z_nat + 1)) 
              ++ decr_string (state_str x) max_char /\
    forall var, 
    var <> x /\ var <> (Z (max_z_nat + 1)) ->
    state_str' var = state_str var).
    {intros cH. destruct cH as [m [m']]. exists (m' + m). 
       rewrite StringLangProperties.compute_program_add. auto. }
    unfold get_str_macro in p_str_decomposition.
    unfold get_decr_macro in p_str_decomposition.

    set (h ++ [StringLang.Instr instr_label (StringLang.APPEND 0 (Z (max_z_nat + 2)))])
    as h'.

    set ((transfer_block (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1)) x (Z (max_z_nat + 1))
    (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1)
    (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char + 1)) (Z (max_z_nat + 2)) max_char ++
    transfer_block (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char + 1)) (Z (max_z_nat + 1)) x
    (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char + 1 + 1)
    (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char + 1 + 1 + max_char + 1)) (Z (max_z_nat + 2))
    max_char ++
    [StringLang.Instr (Some (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char + 1 + 1 + max_char + 1)))
    (StringLang.DEL (Z (max_z_nat + 2)))]) ++ t) as t'.


    pose proof (compute_char_decr max_char p_str (pos_str + 1) state_str x 
    (Z (max_z_nat + 1)) (max_label_nat + max_label_str + 1)
    (max_label_nat + max_label_str + 1 + 1) h' t' (Z (max_z_nat + 2)) a x_value
    (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1))
    (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char + 1)))
    as H_char_decr.
    
    destruct H_char_decr as [char_decr_steps H_char_decr]; auto; try lia.
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
    + exists char_decr_steps. simpl in H_char_decr.
      destruct (StringLang.compute_program p_str (StringLang.SNAP (pos_str + 1) 
      state_str) char_decr_steps) as [char_decr_line char_decr_state].
      simpl in H_char_decr. destruct H_char_decr as [char_cases char_forall].
      destruct char_cases as [case_0_empty | [case_0_nempty | case_S ]].
      (* caso 0 e vazio. basta aplicar diretamente para ir para a transferência *)
      ++ destruct case_0_empty as [char_value [H_x_value_empty [H_char_decr_line 
        [H_char_decr_x H_char_decr_z]]]].
        rewrite H_char_decr_line. 
        replace (max_label_nat + max_label_str + max_char + max_char + 6) with 
        (max_label_nat + max_label_str + 1 + 1 + 
        max_char + 1 + 1 + 1 + max_char + 1) by lia.
        exists 0. rewrite p_str_decomposition. repeat (progress_step).
        repeat (split; auto). rewrite H_char_decr_z. 
        rewrite H_x_value. simpl. rewrite H_x_value_empty. rewrite char_value.
        simpl. rewrite app_nil_r. reflexivity.
      (* caso z e não vazio. volta e aplica indução *)
      ++ destruct case_0_nempty as [char_value [H_x_value_empty [H_char_decr_line 
        [H_char_decr_x H_char_decr_z]]]].
        rewrite H_char_decr_line.
        destruct IHx_value with (state_str := char_decr_state) as [ind_steps H_ind]; 
        auto. destruct string_over_x_value; auto.
        unfold StringLang.state_over. intros var.
        destruct (triple_dec var x (Z (max_z_nat + 1)))
        as [var_eq_x | [var_eq_z | var_diff_all]];
        destruct string_over_x_value.
        rewrite var_eq_x, H_char_decr_x. auto.
        rewrite var_eq_z, H_char_decr_z. 
        StringLang.solve_string. replace (char_decr_state var)
        with (state_str var). auto. symmetry. auto.
        rewrite <- H_aux_value. apply char_forall.
        split. symmetry. rewrite <- var_eqb_neq, x_diff_aux.
        reflexivity. injection. lia.
        replace (StringLang.get_labeled_instr p_str (A (max_label_nat +
        max_label_str + 1))) with (pos_str + 1). exists ind_steps.
        destruct (StringLang.compute_program p_str (StringLang.SNAP 
        (pos_str + 1) char_decr_state) ind_steps) as [ind_line ind_state].
        destruct H_ind as [H_ind_line [H_ind_x [H_ind_z H_ind_forall]]].
        repeat (split; auto).
        * rewrite H_ind_z, H_char_decr_z, H_char_decr_x, H_x_value.
          simpl. destruct x_value; try contradiction.
          rewrite char_value. replace (Nat.ltb 0 0) with false by auto.
          repeat (rewrite <- app_assoc). rewrite cons_app_assoc.
          reflexivity.
        * intros var [var_diff_x var_diff_z]. transitivity (char_decr_state var).
          auto. auto.
        * rewrite p_str_decomposition. repeat (progress_step).
          replace (eqb_opt_lbl instr_label (Some (A (max_label_nat + 
          (max_label_str + 1))))) with false. simpl.
          destruct max_char; simpl; try rewrite PeanoNat.Nat.eqb_refl;
          rewrite H_length; auto. destruct instr_label; auto.
          simpl. destruct l; auto. simpl.
          simpl in label_lt_max_nat. symmetry.
          rewrite PeanoNat.Nat.eqb_neq. lia.
        (* Caso char != 0, basta executar uma transferência *)
      ++ destruct case_S as [char_value [H_char_decr_line [H_char_decr_x 
         H_char_decr_z]]].
         rewrite H_char_decr_line. 
         replace (max_label_nat + max_label_str + max_char + max_char + 6) with 
         (max_label_nat + max_label_str + 1 + 1 + 
         max_char + 1 + 1 + 1 + max_char + 1) by lia. clear h'. clear t'.
         assert (exists n, let (line_str, state_str') :=
         StringLang.split_snap (StringLang.compute_program p_str 
         (StringLang.SNAP (StringLang.get_labeled_instr p_str
         (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1))) 
         char_decr_state) n) in
         line_str = StringLang.get_labeled_instr p_str 
         (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 +
         max_char + 1)) /\
         state_str' x = [] /\
         state_str' (Z (max_z_nat + 1)) =  (char_decr_state (Z (max_z_nat + 1))) ++ 
         (char_decr_state x) /\ forall var, (var <> x /\ var <> (Z (max_z_nat + 1))) -> 
         state_str' var = char_decr_state var) as transfer_computation.
         { remember (h ++
            [StringLang.Instr instr_label (StringLang.APPEND 0 (Z (max_z_nat + 2)))] ++
            get_if_macro_label x (Some (A (max_label_nat + max_label_str + 1))) max_char
            (max_label_nat + max_label_str + 1 + 1) ++
            [StringLang.Instr None
            (StringLang.IF_ENDS_GOTO (Z (max_z_nat + 2)) 0
            (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char + 1)))] ++
            get_all_ai_blocks_decr x (Z (max_z_nat + 1)) (Z (max_z_nat + 2)) max_char
            (max_label_nat + max_label_str + 1 + 1)
            (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1)) ++
            [StringLang.Instr (Some (A (max_label_nat + max_label_str + 1 + 1))) (StringLang.DEL x)] ++
            get_if_macro x None (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1)) max_char ++
            [StringLang.Instr None
            (StringLang.IF_ENDS_GOTO (Z (max_z_nat + 2)) 0
            (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char + 1)))] ++
            [StringLang.Instr (Some (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1)))
            (StringLang.APPEND max_char (Z (max_z_nat + 1)))] ++
            [StringLang.Instr None
            (StringLang.IF_ENDS_GOTO (Z (max_z_nat + 2)) 0 (A (max_label_nat + max_label_str + 1)))])
           as h'.

           remember (transfer_block (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char + 1)) (Z (max_z_nat + 1)) x
            (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char + 1 + 1)
            (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char + 1 + 1 + max_char + 1)) (Z (max_z_nat + 2)) max_char ++
            [StringLang.Instr (Some (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char + 1 + 1 + max_char + 1)))
            (StringLang.DEL (Z (max_z_nat + 2)))] ++ t) as t'.
          
           apply TransferMacroProperties.compute_transfer_block
           with (max_char := max_char) (h := h') (t := t') 
           (aux := (Z (max_z_nat + 2))) (x_value := (char_decr_state x))
           (label_idx := (max_label_nat + max_label_str + 1 + 1 + 
           max_char + 1 + 1))
           (if_goto_idx := (max_label_nat + max_label_str + 1 + 1 + 
           max_char + 1 + 1 + 1)); auto; try lia.
           rewrite p_str_decomposition, Heqh', Heqt'.
           repeat progress_step. reflexivity.
           rewrite Heqh'. repeat (solve_less_than_app).
           rewrite Heqh'. repeat (solve_less_than_app).
           rewrite p_str_decomposition. rewrite Heqh'. repeat (progress_step).
           replace (eqb_opt_lbl instr_label
           (Some (A (max_label_nat + (max_label_str + S (S (max_char + 2)))))))
           with false. repeat (progress_step). destruct max_char.
           simpl. rewrite PeanoNat.Nat.eqb_refl. 
           rewrite length_app. reflexivity.
           simpl. rewrite PeanoNat.Nat.eqb_refl. 
           repeat (rewrite length_app; simpl). reflexivity. 
           simpl. destruct instr_label; auto.
           destruct l. simpl in label_lt_max_nat. simpl. symmetry.
           rewrite PeanoNat.Nat.eqb_neq. lia.
           unfold StringLang.state_over. intros var.
          destruct (triple_dec var x (Z (max_z_nat + 1)))
          as [var_eq_x | [var_eq_z | var_diff_all]];
          destruct string_over_x_value.
          rewrite var_eq_x, H_char_decr_x. auto.
          rewrite var_eq_z, H_char_decr_z. 
          StringLang.solve_string. lia.
          replace (char_decr_state var) with (state_str var). 
          auto. symmetry. auto.
          replace (char_decr_state (Z (max_z_nat + 2))) 
          with (state_str (Z (max_z_nat + 2))). rewrite H_aux_value.
          reflexivity. symmetry. apply char_forall. 
          split. symmetry. rewrite <- var_eqb_neq, x_diff_aux.
          reflexivity. injection. lia. simpl. 
          rewrite PeanoNat.Nat.eqb_neq. lia. }
        destruct transfer_computation as [transfer_steps H_transfer].
        exists transfer_steps.
        destruct ((StringLang.compute_program p_str (StringLang.SNAP
        (StringLang.get_labeled_instr p_str
        (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1)))
        char_decr_state) transfer_steps)) as [transfer_line transfer_state].
        destruct H_transfer as [H_line_transfer [H_state_x [H_state_z
        H_forall]]]. rewrite H_line_transfer. simpl.
        repeat (split; auto). rewrite H_state_z.
        rewrite H_char_decr_x, H_char_decr_z, H_x_value.
        simpl. destruct x_value. 
        replace (Nat.eqb a 0 ) with false. rewrite app_nil_r.
        reflexivity. symmetry. rewrite PeanoNat.Nat.eqb_neq. lia.
        replace (Nat.ltb 0 a) with true. rewrite <- app_assoc.
        simpl. reflexivity. symmetry. rewrite PeanoNat.Nat.ltb_lt. lia.
        intros var [var_diff_x var_diff_z].
        transitivity (char_decr_state var). auto. auto.
Qed.



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
  intros max_char p_str pos_str state_str instr_label x 
  max_label_nat max_z_nat h t x_value max_label_str.
  intros p_str_decomposition H_length label_lt_max_nat
  H_state_over string_over_x_value H_x_value H_aux_value 
  x_diff_aux x_diff_z.

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
     (NatLang.Instr instr_label (NatLang.DECR x)) max_char /\
      state_str' x = state_str (Z (max_z_nat + 1)) ++ decr_string (state_str x)
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
  pose proof (compute_decr_macro_aux
  max_char p_str pos_str one_step_state instr_label x max_label_nat max_z_nat
  h t x_value) as H_decr_aux. simpl in H_decr_aux. 
  destruct H_decr_aux as [decr_aux_steps H_decr_aux]; auto.
  rewrite Heqone_step_state. StringLang.solve_string. lia.
  rewrite Heqone_step_state. solve_var_equation. auto.
  rewrite Heqone_step_state. solve_var_equation. rewrite H_aux_value. auto.
  exists decr_aux_steps. rewrite <- p_str_decomposition. 
  rewrite <- H_length in H_decr_aux.
  destruct ((StringLang.compute_program p_str (StringLang.SNAP (length h + 1)
  one_step_state) decr_aux_steps)). simpl. simpl in H_decr_aux.
  destruct H_decr_aux as [Hn [Hsx [Hsz1 Hsforall]]].
  repeat (rewrite cons_app_assoc in p_str_decomposition).

  set (h ++
  [StringLang.Instr instr_label (StringLang.APPEND 0 (Z (max_z_nat + 2)))] ++
  (get_if_macro_label x (Some (A (max_label_nat + max_label_str + 1))) max_char (max_label_nat + max_label_str + 1 + 1) ++
  [StringLang.Instr None
  (StringLang.IF_ENDS_GOTO (Z (max_z_nat + 2)) 0
  (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char + 1)))] ++
  get_all_ai_blocks_decr x (Z (max_z_nat + 1)) (Z (max_z_nat + 2)) max_char (max_label_nat + max_label_str + 1 + 1)
  (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1)) ++
  [StringLang.Instr (Some (A (max_label_nat + max_label_str + 1 + 1))) (StringLang.DEL x)] ++
  get_if_macro x None (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1)) max_char ++
  [StringLang.Instr None
  (StringLang.IF_ENDS_GOTO (Z (max_z_nat + 2)) 0
  (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char + 1)))] ++
  [StringLang.Instr (Some (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1)))
  (StringLang.APPEND max_char (Z (max_z_nat + 1)))] ++
  [StringLang.Instr None (StringLang.IF_ENDS_GOTO (Z (max_z_nat + 2)) 0 (A (max_label_nat + max_label_str + 1)))] ++
  transfer_block (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1)) x (Z (max_z_nat + 1))
  (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1)
  (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char + 1)) (Z (max_z_nat + 2)) max_char))
  as h'.

  set ([StringLang.Instr (Some (A (max_label_nat + max_label_str + 1 + 1 + 
  max_char + 1 + 1 + 1 + max_char + 1 + 1 + max_char + 1))) (StringLang.DEL (Z (max_z_nat + 2)))]
   ++ [] ++ t) as t'.

  (* 3. Usando Lema para executar transferência de Z 
        para X *)
  pose proof (TransferMacroProperties.compute_transfer_block
  max_char p_str n s
  (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char + 1)
  (Z (max_z_nat + 1)) x
  (A (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char + 1 + 1 +
  max_char + 1))
  (max_label_nat + max_label_str + 1 + 1 + max_char + 1 + 1 + 1 + max_char + 1 + 1)
  h' t' (Z (max_z_nat + 2)) (s (Z (max_z_nat + 1)))) as 
  H_transfer. unfold max_label_str in *.

  destruct H_transfer as [transfer_steps H_transfer]; auto.
  rewrite p_str_decomposition. unfold h', t'. aac_reflexivity.
  unfold h'. repeat (solve_less_than_app).
  unfold h'. repeat (solve_less_than_app).
  lia.
  unfold h'. rewrite Hn, p_str_decomposition.
  repeat (rewrite <- app_assoc).
  repeat(rewrite_labeled_instr_app).
  replace (max_label_nat + StringUtils.get_max_label h + max_char + 
  max_char + 6) 
  with (max_label_nat + StringUtils.get_max_label h + 1 + 1 + max_char + 1 + 1 + 1 +
max_char + 1) by lia.
  rewrite get_labeled_instr_transfer.
  repeat (rewrite length_app). lia.
  unfold StringLang.state_over. intros x0.
  destruct (triple_dec x0 x (Z (max_z_nat + 1))).
  rewrite H, Hsx. reflexivity. destruct H.
  rewrite H, Hsz1, Heqone_step_state. 
  StringLang.solve_string. lia.
  apply decr_string_over. StringLang.solve_string. lia.
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
  assert (eqb_opt_lbl instr_label (Some
  (A (max_label_nat + (StringUtils.get_max_label h +
  S (S (max_char + S (S (S (max_char + S (S (max_char + 1)))))))))))= false) as 
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

