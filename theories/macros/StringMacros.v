From Stdlib Require Import List Lia.
From Triq Require Import LanguagesCommon StringUtils.
From Triq.string_lang Require StringLang.
Import ListNotations.


Module Type TStringMacros.
  Parameter low_z high_z low_label high_label max_char : nat.
  Axiom z_range_valid : low_z <= high_z.
  Axiom label_range_valid : low_label <= high_label.
  Parameter program : StringLang.program.
  Axiom variables_range : forall o s k,
    In (StringLang.Instr o s) program -> statement_variable s = Z k ->
    low_z <= k /\ k <= high_z.
  Axiom labels_range : forall s k,
    In (StringLang.Instr (Some (A k)) s) program ->
    low_label <= k /\ k <= high_label.
  Axiom alphabet : StringLang.program_over program max_char.
  Axiom internal_jumps : forall o v c l,
    In (StringLang.Instr o (StringLang.IF_ENDS_GOTO v c l)) program ->
    has_labeled_instr program l = true.
End TStringMacros.


Lemma next_step_in_context (macro : StringLang.program)
  (internal_jumps : forall o v c l,
    In (StringLang.Instr o (StringLang.IF_ENDS_GOTO v c l)) macro ->
    has_labeled_instr macro l = true)
  (prefix suffix : StringLang.program)
  (no_shadow : forall l,
    has_labeled_instr macro l = true ->
    has_labeled_instr prefix l = false) : forall pc st,
  pc < length macro ->
  let '(StringLang.SNAP pc' st') :=
    StringLang.next_step macro (StringLang.SNAP pc st) in
  pc' <= length macro /\
  StringLang.next_step (prefix ++ macro ++ suffix)
    (StringLang.SNAP (length prefix + pc) st) =
    StringLang.SNAP (length prefix + pc') st'.
Proof.
  intros pc st Hpc. unfold StringLang.next_step.
  rewrite nth_error_in_context by exact Hpc.
  destruct (nth_error macro pc) as [[o s]|] eqn:E.
  - destruct s; simpl; try (split; [lia|f_equal; lia]).
    destruct (StringLang.ends_with (st v) n); simpl.
    + assert (Hlabel : has_labeled_instr macro l = true).
      { eapply internal_jumps. eapply nth_error_In; eauto. }
      split.
      * pose proof (get_labeled_instr_present _ _ Hlabel). lia.
      * rewrite get_labeled_instr_app by (apply no_shadow; exact Hlabel).
        rewrite get_labeled_instr_app_present by exact Hlabel. reflexivity.
    + split; [lia|f_equal; lia].
  - apply nth_error_None in E. lia.
Qed.

(** Ao terminar isoladamente, a macro fica parada. No contexto, porém,
    o próximo passo executaria o sufixo. Por isso contamos apenas os
    passos até a saída, descartando eventuais passos parados. *)
Lemma compute_in_context (macro : StringLang.program)
  (internal_jumps : forall o v c l,
    In (StringLang.Instr o (StringLang.IF_ENDS_GOTO v c l)) macro ->
    has_labeled_instr macro l = true)
  (prefix suffix : StringLang.program)
  (no_shadow : forall l,
    has_labeled_instr macro l = true ->
    has_labeled_instr prefix l = false) : forall steps pc st,
  pc <= length macro ->
  let '(StringLang.SNAP pc' st') :=
    StringLang.compute_program macro (StringLang.SNAP pc st) steps in
  pc' <= length macro /\
  exists used_steps, used_steps <= steps /\
    StringLang.compute_program (prefix ++ macro ++ suffix)
      (StringLang.SNAP (length prefix + pc) st) used_steps =
      StringLang.SNAP (length prefix + pc') st'.
Proof.
  induction steps as [|steps IH]; intros pc st Hpc; simpl.
  - split; auto. exists 0. simpl; auto.
  - specialize (IH pc st Hpc).
    destruct (StringLang.compute_program macro (StringLang.SNAP pc st) steps)
      as [pc' st'] eqn:E.
    destruct IH as [Hbound [used [Hused Hrun]]].
    destruct (PeanoNat.Nat.eq_dec pc' (length macro)) as [Hend|Hinside].
    + subst pc'. unfold StringLang.next_step.
      assert (Hnone : nth_error macro (length macro) = None)
        by (apply nth_error_None; lia).
      rewrite Hnone.
      split; auto. exists used. split; auto; lia.
    + pose proof (next_step_in_context macro internal_jumps prefix suffix no_shadow pc' st' ltac:(lia)) as Hstep.
      destruct (StringLang.next_step macro (StringLang.SNAP pc' st'))
        as [pc'' st''] eqn:Estep.
      destruct Hstep as [Hbound' Hstep]. split; auto.
      exists (S used). split; [lia|]. simpl. rewrite Hrun. exact Hstep.
Qed.

(** Teorema principal: o estado final é exatamente o mesmo, inclusive
    nas variáveis auxiliares. A execução no contexto para na entrada
    do sufixo, sem executar suas instruções. *)
Theorem macro_in_context (macro : StringLang.program)
  (internal_jumps : forall o v c l,
    In (StringLang.Instr o (StringLang.IF_ENDS_GOTO v c l)) macro ->
    has_labeled_instr macro l = true)
  (prefix suffix : StringLang.program)
  (no_shadow : forall l,
    has_labeled_instr macro l = true ->
    has_labeled_instr prefix l = false) : forall st result steps,
  StringLang.compute_program macro (StringLang.SNAP 0 st) steps =
    StringLang.SNAP (length macro) result ->
  exists used_steps, used_steps <= steps /\
    StringLang.compute_program (prefix ++ macro ++ suffix)
      (StringLang.SNAP (length prefix) st) used_steps =
      StringLang.SNAP (length prefix + length macro) result.
Proof.
  intros st result steps Hrun.
  pose proof (compute_in_context macro internal_jumps prefix suffix no_shadow steps 0 st ltac:(lia)) as H.
  rewrite Hrun in H. simpl in H.
  replace (length prefix + 0) with (length prefix) in H by lia.
  exact (proj2 H).
Qed.

(** A relação de estados acompanha o deslocamento dos nomes locais. *)
Definition shifted_state dz (old new : StringLang.state) :=
  forall v, new (shift_variable dz v) = old v.

Definition unshift_state dz (st : StringLang.state) : StringLang.state :=
  fun v => st (shift_variable dz v).

Lemma shift_update : forall dz old new v value,
  shifted_state dz old new ->
  shifted_state dz (StringLang.update old v value)
    (StringLang.update new (shift_variable dz v) value).
Proof.
  intros dz old new v value H w. unfold StringLang.update.
  rewrite shift_variable_eqb. destruct (eqb_var v w); auto.
Qed.

Lemma shift_next_step : forall p dz dl pc old new,
  shifted_state dz old new ->
  let '(StringLang.SNAP pc1 old1) := StringLang.next_step p (StringLang.SNAP pc old) in
  let '(StringLang.SNAP pc2 new1) :=
    StringLang.next_step (shift_program dz dl p) (StringLang.SNAP pc new) in
  pc1 = pc2 /\ shifted_state dz old1 new1.
Proof.
  intros p dz dl pc old new H. unfold StringLang.next_step.
  rewrite shift_nth_error.
  destruct (nth_error p pc) as [[o s]|]; simpl; auto.
  destruct s; simpl.
  - split; auto. unfold StringLang.append. rewrite H. apply shift_update; auto.
  - split; auto. unfold StringLang.del. rewrite H. apply shift_update; auto.
  - rewrite H. destruct (StringLang.ends_with (old v) n); split; auto.
    symmetry. apply shift_label_position.
Qed.

Lemma shift_compute : forall p dz dl steps pc old new,
  shifted_state dz old new ->
  let '(StringLang.SNAP pc1 old1) :=
    StringLang.compute_program p (StringLang.SNAP pc old) steps in
  let '(StringLang.SNAP pc2 new1) :=
    StringLang.compute_program (shift_program dz dl p) (StringLang.SNAP pc new) steps in
  pc1 = pc2 /\ shifted_state dz old1 new1.
Proof.
  intros p dz dl steps. induction steps as [|steps IH]; intros pc old new H; simpl; auto.
  specialize (IH pc old new H).
  destruct (StringLang.compute_program p (StringLang.SNAP pc old) steps) as [pc1 old1].
  destruct (StringLang.compute_program (shift_program dz dl p)
    (StringLang.SNAP pc new) steps) as [pc2 new1].
  destruct IH as [E Hstates]. subst pc2. apply shift_next_step; auto.
Qed.

Module StringMacroProperties (M : TStringMacros).
  Definition shift dz dl := shift_program dz dl M.program.

  Lemma shifted_variables_range : forall dz dl o s k,
    In (StringLang.Instr o s) (shift dz dl) -> statement_variable s = Z k ->
    dz + M.low_z <= k /\ k <= dz + M.high_z.
  Proof.
    intros dz dl o s k Hin Hvar.
    apply in_map_iff in Hin. destruct Hin as [[o' s'] [E Hin]].
    destruct s'; simpl in E; inversion E; subst;
      destruct v; simpl in Hvar; try discriminate;
      injection Hvar as Hk; subst k;
      pose proof (M.variables_range _ _ _ Hin eq_refl); lia.
  Qed.

  Lemma shifted_next_step_preserves_outside : forall dz dl k pc st,
    k < dz + M.low_z \/ dz + M.high_z < k ->
    let '(StringLang.SNAP _ st') :=
      StringLang.next_step (shift dz dl) (StringLang.SNAP pc st) in st' (Z k) = st (Z k).
  Proof.
    intros dz dl k pc st Houtside. unfold StringLang.next_step.
    destruct (nth_error (shift dz dl) pc) as [[o s]|] eqn:E; auto.
    assert (Hvar : statement_variable s <> Z k).
    { intros Hvar. pose proof (shifted_variables_range dz dl o s k
        (nth_error_In _ _ E) Hvar). lia. }
    destruct s; simpl in Hvar; simpl.
    - unfold StringLang.append, StringLang.update.
      apply var_eqb_neq in Hvar. rewrite Hvar. reflexivity.
    - unfold StringLang.del, StringLang.update.
      apply var_eqb_neq in Hvar. rewrite Hvar. reflexivity.
    - destruct (StringLang.ends_with (st v) n); reflexivity.
  Qed.

  Lemma shifted_preserves_outside : forall dz dl k steps pc st,
    k < dz + M.low_z \/ dz + M.high_z < k ->
    let '(StringLang.SNAP _ st') :=
      StringLang.compute_program (shift dz dl) (StringLang.SNAP pc st) steps in
    st' (Z k) = st (Z k).
  Proof.
    intros dz dl k steps. induction steps as [|steps IH]; intros pc st Houtside; simpl; auto.
    specialize (IH pc st Houtside).
    destruct (StringLang.compute_program (shift dz dl) (StringLang.SNAP pc st) steps)
      as [pc' st'].
    pose proof (shifted_next_step_preserves_outside dz dl k pc' st' Houtside) as Hstep.
    destruct (StringLang.next_step (shift dz dl) (StringLang.SNAP pc' st')).
    simpl in *. congruence.
  Qed.

  Lemma shifted_labels_range : forall dz dl s k,
    In (StringLang.Instr (Some (A k)) s) (shift dz dl) ->
    dl + M.low_label <= k /\ k <= dl + M.high_label.
  Proof.
    intros dz dl s k Hin. apply in_map_iff in Hin.
    destruct Hin as [[o s'] [E Hin]].
    destruct o as [[j]|]; simpl in E; try discriminate.
    injection E as Hlabel Hs. inversion Hlabel; subst k.
    pose proof (M.labels_range _ _ Hin). lia.
  Qed.

  Lemma shifted_alphabet : forall dz dl,
    StringLang.program_over (shift dz dl) M.max_char.
  Proof.
    intros dz dl. unfold shift, shift_program.
    pose proof M.alphabet as H. induction M.program as [|[o s] p IH]; simpl in *; auto.
    destruct s; simpl in *; intuition.
  Qed.

  Lemma shifted_internal_jumps : forall dz dl o v c l,
    In (StringLang.Instr o (StringLang.IF_ENDS_GOTO v c l)) (shift dz dl) ->
    has_labeled_instr (shift dz dl) l = true.
  Proof.
    intros dz dl o v c l Hin. apply in_map_iff in Hin.
    destruct Hin as [[o' s] [E Hin]].
    destruct s; simpl in E; try discriminate. inversion E; subst.
    unfold shift. rewrite shift_has_label. eapply M.internal_jumps; eauto.
  Qed.

  (** O range deslocado fica acima das labels do prefixo. *)
  Lemma shift_no_shadow : forall dz dl prefix,
    get_max_label prefix < dl + M.low_label ->
    forall l, has_labeled_instr (shift dz dl) l = true ->
      has_labeled_instr prefix l = false.
  Proof.
    intros dz dl prefix Hfresh [k] Hlabel.
    destruct (has_labeled_instr_in _ _ Hlabel) as [s Hin].
    pose proof (shifted_labels_range dz dl s k Hin) as Hrange.
    eapply labels_less_implies_diff with (value := dl + M.low_label); [|lia].
    apply labels_leq_max; exact Hfresh.
  Qed.

  (** Indexação após SHIFT e inserção no contexto. *)
  Lemma shifted_instruction_position : forall dz dl prefix suffix pc,
    pc < length M.program ->
    nth_error (prefix ++ shift dz dl ++ suffix) (length prefix + pc) =
    option_map (shift_instruction dz dl) (nth_error M.program pc).
  Proof.
    intros. unfold shift. rewrite nth_error_in_context by (rewrite shift_length; assumption).
    apply shift_nth_error.
  Qed.

  Lemma shifted_label_position : forall dz dl prefix suffix l,
    get_max_label prefix < dl + M.low_label ->
    has_labeled_instr M.program l = true ->
    StringLang.get_labeled_instr (prefix ++ shift dz dl ++ suffix) (shift_label dl l) =
    length prefix + StringLang.get_labeled_instr M.program l.
  Proof.
    intros dz dl prefix suffix l Hfresh Hl. unfold shift.
    assert (Hshift : has_labeled_instr (shift dz dl) (shift_label dl l) = true)
      by (unfold shift; rewrite shift_has_label; exact Hl).
    rewrite get_labeled_instr_app by
      exact (shift_no_shadow dz dl prefix Hfresh (shift_label dl l) Hshift).
    rewrite get_labeled_instr_app_present by exact Hshift.
    rewrite shift_label_position. reflexivity.
  Qed.

  (** Executar a macro original e inserir seu SHIFT produzem a mesma
      alteração nos nomes correspondentes.  *)
  Theorem shifted_macro_in_context : forall dz dl prefix suffix st result steps,
    get_max_label prefix < dl + M.low_label ->
    StringLang.compute_program M.program (StringLang.SNAP 0 (unshift_state dz st)) steps =
      StringLang.SNAP (length M.program) result ->
    exists used_steps final_state,
      used_steps <= steps /\
      StringLang.compute_program (prefix ++ shift dz dl ++ suffix)
        (StringLang.SNAP (length prefix) st) used_steps =
        StringLang.SNAP (length prefix + length M.program) final_state /\
      shifted_state dz result final_state /\
      (forall k, k < dz + M.low_z \/ dz + M.high_z < k ->
        final_state (Z k) = st (Z k)).
  Proof.
    intros dz dl prefix suffix st result steps Hfresh Hrun. unfold shift in *.
    pose proof (shift_compute M.program dz dl steps 0 (unshift_state dz st) st
      ltac:(intros v; reflexivity)) as Hshift.
    rewrite Hrun in Hshift.
    destruct (StringLang.compute_program (shift_program dz dl M.program) (StringLang.SNAP 0 st) steps)
      as [pc final_state] eqn:E.
    destruct Hshift as [Hpc Hstate]. subst pc.
    assert (Hend : StringLang.compute_program (shift dz dl) (StringLang.SNAP 0 st) steps =
      StringLang.SNAP (length (shift dz dl)) final_state).
    { unfold shift in *. rewrite shift_length. exact E. }
    destruct (macro_in_context (shift dz dl) (shifted_internal_jumps dz dl)
      prefix suffix (shift_no_shadow dz dl prefix Hfresh) st final_state steps Hend)
      as [used [Hused Hcontext]].
    exists used, final_state. unfold shift in Hcontext. rewrite shift_length in Hcontext.
    repeat split; auto. intros k Houtside.
    pose proof (shifted_preserves_outside dz dl k steps 0 st Houtside) as Houtside'.
    unfold shift in Houtside'. rewrite E in Houtside'. exact Houtside'.
  Qed.
  (** O deslocamento dos labels é escolhido acima dos labels do prefixo. *)
  Corollary fresh_macro_in_context : forall dz prefix suffix st result steps,
    StringLang.compute_program M.program
      (StringLang.SNAP 0 (unshift_state dz st)) steps =
      StringLang.SNAP (length M.program) result ->
    exists used_steps final_state,
      used_steps <= steps /\
      StringLang.compute_program
        (prefix ++ shift dz (S (get_max_label prefix)) ++ suffix)
        (StringLang.SNAP (length prefix) st) used_steps =
        StringLang.SNAP (length prefix + length M.program) final_state /\
      shifted_state dz result final_state /\
      (forall k, k < dz + M.low_z \/ dz + M.high_z < k ->
        final_state (Z k) = st (Z k)).
  Proof.
    intros dz prefix suffix st result steps Hrun.
    apply shifted_macro_in_context.
    - lia.
    - exact Hrun.
  Qed.
End StringMacroProperties.

(** Exemplo: os limites pertencem à própria implementação; o programa
    é escrito em função deles e depois deslocado por SHIFT. *)
Module AppendLocal <: TStringMacros.
  Definition low_z := 2.
  Definition high_z := 4.
  Definition low_label := 3.
  Definition high_label := 5.
  Definition max_char := 1.

  Lemma z_range_valid : low_z <= high_z. 
  Proof. 
    unfold low_z, high_z; lia. 
  Qed.

  Lemma label_range_valid : low_label <= high_label.
  Proof. 
    unfold low_label, high_label; lia. 
  Qed
  .
  Definition program : StringLang.program :=
    [StringLang.Instr (Some (A low_label)) (StringLang.APPEND 0 (Z low_z))].

  Lemma variables_range : forall o s k,
    In (StringLang.Instr o s) program -> statement_variable s = Z k ->
    low_z <= k /\ k <= high_z.
  Proof.
    intros o s k [E|H] Hvar; [|contradiction].
    inversion E; subst. simpl in Hvar. injection Hvar as Ek; subst. split; [lia|apply z_range_valid].
  Qed.

  Lemma labels_range : forall s k,
    In (StringLang.Instr (Some (A k)) s) program -> low_label <= k /\ k <= high_label.
  Proof.
    intros s k [E|H]; [|contradiction]. inversion E; subst.
    split; [lia|apply label_range_valid].
  Qed.

  Lemma alphabet : StringLang.program_over program max_char.
  Proof. 
    simpl; auto with arith. 
  Qed.

  Lemma internal_jumps : forall o v c l,
    In (StringLang.Instr o (StringLang.IF_ENDS_GOTO v c l)) program ->
    has_labeled_instr program l = true.
  Proof. 
    intros o v c l [H|H]; discriminate || contradiction. 
  Qed.
End AppendLocal.

Module ExampleProperties := StringMacroProperties AppendLocal.

Example shifted_append_local : ExampleProperties.shift 10 20 =
  [StringLang.Instr (Some (A 23)) (StringLang.APPEND 0 (Z 12))].
Proof. reflexivity. Qed.

Example append_local_in_context : forall prefix suffix st,
  exists steps final_state,
    steps <= 1 /\
    StringLang.compute_program
      (prefix ++ ExampleProperties.shift 10 (S (get_max_label prefix)) ++ suffix)
      (StringLang.SNAP (length prefix) st) steps =
      StringLang.SNAP (length prefix + 1) final_state /\
    final_state (Z 12) = st (Z 12) ++ [0] /\
    (forall k, k < 12 \/ 14 < k -> final_state (Z k) = st (Z k)).
Proof.
  intros prefix suffix st.
  destruct (ExampleProperties.fresh_macro_in_context 10 prefix suffix st
    (StringLang.append 0 (unshift_state 10 st) (Z 2)) 1 eq_refl)
    as [steps [final_state [Hsteps [Hrun [Hstate Houtside]]]]].
  exists steps, final_state. repeat split; auto.
  exact (Hstate (Z 2)).
Qed.