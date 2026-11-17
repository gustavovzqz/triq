From Stdlib Require Import List Lia.
From Triq Require Import LanguagesCommon StringUtils.
From Triq.string_lang Require StringLang.
Import ListNotations.


(*
  Expansão da Macro 

  Z (z_shift) = variável de saída
  Z (z_shift + 1) até (z_shift + n_input) são as variáveis de entrada
  Z (z_shift + n_input + 1) até Z (z_shift + n_input + n_aux) são as variáveis auxiliares

  Na expansão:
    1. Atribuímos as variáveis de entrada (parâmetros da expansão) às entradas da macro e zeramos a saída
       Z (shift)           <- 0
       Z (shift + 1)       <- arg1
       Z (shift + 2)       <- arg2
                      ...
       Z (shift + n_input) <- arg_n_input

    2. Zeramos as variáveis auxiliares e 
       Z (shift + n_input + 1)     <- 0
                      ...
       Z (shift + n_input + n_aux) <- 0

    3. Expandimos a macro

    4. Atribuímos o valor em Z (shift) para a variável de saída declarada como argumento da expansão
       X_saida <- Z (shift)
      

*)

Module Type TStringMacros.
  Parameter z_shift l_shift n_input n_aux n_labels max_char : nat.
  Parameter program : StringLang.program.

  (* Não ocorrem variáveis do tipo X e Y no programa, apenas Z *)
  Axiom variables_local : forall o s,
    In (StringLang.Instr o s) program ->
    exists k, statement_variable s = Z k.

  (* Toda variável que ocorre dentro do programa está entre o shift 
     e shift + n_input + n_aux *)
  Axiom variables_range : forall o s k,
    In (StringLang.Instr o s) program -> 
    statement_variable s = Z k ->
    z_shift <= k /\ k <= z_shift + n_input + n_aux.

  (* As labels também estão no limite [l_shift, l_shift + n_labels) *)
  Axiom labels_range : forall s k,
    In (StringLang.Instr (Some (A k)) s) program ->
    l_shift <= k /\ k < l_shift + n_labels.

  (* Delimita o alfabeto usado pelo programa *)
  Axiom alphabet : StringLang.program_over program max_char.

  (* Todos os pulos são internos. *)
  Axiom internal_jumps : forall o v c l,
    In (StringLang.Instr o (StringLang.IF_ENDS_GOTO v c l)) program ->
    has_labeled_instr program l = true.
End TStringMacros.

(** Uma macro com especificação de sua saída e garantia de término.
    A propriedade depende das entradas INICIAIS, pois a execução pode
    modificar tanto as entradas locais quanto as variáveis auxiliares. *)
Module Type TStringMacroWithSpec.
  Include TStringMacros.

  (** Entradas na ordem Z (z_shift + 1), ..., Z (z_shift + n_input). *)
  Definition input_values (st : StringLang.state) : list StringLang.string :=
    map (fun i => st (Z (z_shift + S i))) (seq 0 n_input).

  (** Apenas a saída e as auxiliares locais precisam começar vazias.
      As entradas e as variáveis fora da macro têm valores arbitrários.
      Em StringLang, o valor nulo é a string vazia [], e não [0]. *)
  Definition precondition (st : StringLang.state) : Prop :=
    st (Z z_shift) = [] /\
    forall k, z_shift + n_input < k <= z_shift + n_input + n_aux ->
      st (Z k) = [].

  (** Relaciona as entradas iniciais com a saída final *)
  Parameter postcondition : list StringLang.string -> StringLang.string -> Prop.

  (** Cada implementação deve provar este contrato: a execução termina
      e sua saída satisfaz a propriedade declarada. *)
  Axiom execution_correct : forall initial,
    precondition initial ->
    exists steps final,
      StringLang.compute_program program (StringLang.SNAP 0 initial) steps =
        StringLang.SNAP (length program) final /\
      postcondition (input_values initial) (final (Z z_shift)).
End TStringMacroWithSpec.

(** Um passo interno da macro coincide com o passo no programa maior. *)
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

(** Atualizações correspondentes preservam a relação entre estados deslocados. *)
Lemma shift_update : forall dz old new v value,
  shifted_state dz old new ->
  shifted_state dz (StringLang.update old v value)
    (StringLang.update new (shift_variable dz v) value).
Proof.
  intros dz old new v value H w. unfold StringLang.update.
  rewrite shift_variable_eqb. destruct (eqb_var v w); auto.
Qed.

(** Um passo preserva o contador e a correspondência dos estados. *)
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

(** A simulação de um passo estende-se a qualquer número de passos. *)
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

  (** A variável de uma instrução deslocada continua sendo local. *)
  Lemma shifted_variables_local : forall dz dl o s,
    In (StringLang.Instr o s) (shift dz dl) ->
    exists k, statement_variable s = Z k /\
      dz + M.z_shift <= k /\ k <= dz + M.z_shift + M.n_input + M.n_aux.
  Proof.
    intros dz dl o s Hin.
    apply in_map_iff in Hin. destruct Hin as [[o' s'] [E Hin]].
    destruct s'; simpl in E; inversion E; subst;
      destruct (M.variables_local _ _ Hin) as [k Hk];
      destruct v as [i|i|]; simpl in Hk; try discriminate;
      injection Hk as Heq; subst;
      exists (dz + k); simpl; repeat split;
      pose proof (M.variables_range _ _ _ Hin eq_refl); lia.
  Qed.

  Definition outside dz (v : variable) : Prop :=
    match v with
    | Z k => k < dz + M.z_shift \/ dz + M.z_shift + M.n_input + M.n_aux < k
    | _ => True
    end.

  (** Um passo não modifica variáveis fora do intervalo local. *)
  Lemma shifted_next_step_preserves_outside : forall dz dl v pc st,
    outside dz v ->
    let '(StringLang.SNAP _ st') :=
      StringLang.next_step (shift dz dl) (StringLang.SNAP pc st) in st' v = st v.
  Proof.
    intros dz dl v pc st Houtside. unfold StringLang.next_step.
    destruct (nth_error (shift dz dl) pc) as [[o s]|] eqn:E; auto.
    assert (Hvar : statement_variable s <> v).
    { intros Hvar.
      destruct (shifted_variables_local dz dl o s (nth_error_In _ _ E))
        as [k [Hlocal Hrange]].
      rewrite Hvar in Hlocal. destruct v; simpl in Houtside;
        try discriminate. injection Hlocal as Heq; subst; lia. }
    destruct s; simpl in Hvar; simpl.
    - unfold StringLang.append, StringLang.update.
      apply var_eqb_neq in Hvar. rewrite Hvar. reflexivity.
    - unfold StringLang.del, StringLang.update.
      apply var_eqb_neq in Hvar. rewrite Hvar. reflexivity.
    - destruct (StringLang.ends_with (st v0) n); reflexivity.
  Qed.

  (** Uma execução inteira preserva variáveis fora do intervalo local. *)
  Lemma shifted_preserves_outside : forall dz dl v steps pc st,
    outside dz v ->
    let '(StringLang.SNAP _ st') :=
      StringLang.compute_program (shift dz dl) (StringLang.SNAP pc st) steps in
    st' v = st v.
  Proof.
    intros dz dl v steps. induction steps as [|steps IH]; intros pc st Houtside; simpl; auto.
    specialize (IH pc st Houtside).
    destruct (StringLang.compute_program (shift dz dl) (StringLang.SNAP pc st) steps)
      as [pc' st'].
    pose proof (shifted_next_step_preserves_outside dz dl v pc' st' Houtside) as Hstep.
    destruct (StringLang.next_step (shift dz dl) (StringLang.SNAP pc' st')).
    simpl in *. congruence.
  Qed.

  (** As marcas deslocadas ficam no intervalo reservado. *)
  Lemma shifted_labels_range : forall dz dl s k,
    In (StringLang.Instr (Some (A k)) s) (shift dz dl) ->
    dl + M.l_shift <= k /\ k < dl + M.l_shift + M.n_labels.
  Proof.
    intros dz dl s k Hin. apply in_map_iff in Hin.
    destruct Hin as [[o s'] [E Hin]].
    destruct o as [[j]|]; simpl in E; try discriminate.
    injection E as Hlabel Hs. inversion Hlabel; subst k.
    pose proof (M.labels_range _ _ Hin). lia.
  Qed.

  (** Saltos internos continuam apontando para marcas da macro deslocada. *)
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
    get_max_label prefix < dl + M.l_shift ->
    forall l, has_labeled_instr (shift dz dl) l = true ->
      has_labeled_instr prefix l = false.
  Proof.
    intros dz dl prefix Hfresh [k] Hlabel.
    destruct (has_labeled_instr_in _ _ Hlabel) as [s Hin].
    pose proof (shifted_labels_range dz dl s k Hin) as Hrange.
    eapply labels_less_implies_diff with (value := dl + M.l_shift); [|lia].
    apply labels_leq_max; exact Hfresh.
  Qed.

  (** Executar a macro original e inserir seu SHIFT produzem a mesma
      alteração nos nomes correspondentes.  *)
  Theorem shifted_macro_in_context_no_shadow : forall dz dl prefix suffix st result steps,
    (forall l, has_labeled_instr (shift dz dl) l = true ->
      has_labeled_instr prefix l = false) ->
    StringLang.compute_program M.program (StringLang.SNAP 0 (unshift_state dz st)) steps =
      StringLang.SNAP (length M.program) result ->
    exists used_steps final_state,
      used_steps <= steps /\
      StringLang.compute_program (prefix ++ shift dz dl ++ suffix)
        (StringLang.SNAP (length prefix) st) used_steps =
        StringLang.SNAP (length prefix + length M.program) final_state /\
      shifted_state dz result final_state /\
      (forall v, outside dz v -> final_state v = st v).
  Proof.
    intros dz dl prefix suffix st result steps Hshadow Hrun. unfold shift in *.
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
      prefix suffix Hshadow st final_state steps Hend)
      as [used [Hused Hcontext]].
    exists used, final_state. unfold shift in Hcontext. rewrite shift_length in Hcontext.
    repeat split; auto. intros v Houtside.
    pose proof (shifted_preserves_outside dz dl v steps 0 st Houtside) as Houtside'.
    unfold shift in Houtside'. rewrite E in Houtside'. exact Houtside'.
  Qed.
  (** Limites de rótulos fornecem uma forma simples de garantir frescor. *)
  Theorem shifted_macro_in_context : forall dz dl prefix suffix st result steps,
    get_max_label prefix < dl + M.l_shift ->
    StringLang.compute_program M.program (StringLang.SNAP 0 (unshift_state dz st)) steps =
      StringLang.SNAP (length M.program) result ->
    exists used_steps final_state,
      used_steps <= steps /\
      StringLang.compute_program (prefix ++ shift dz dl ++ suffix)
        (StringLang.SNAP (length prefix) st) used_steps =
        StringLang.SNAP (length prefix + length M.program) final_state /\
      shifted_state dz result final_state /\
      (forall v, outside dz v -> final_state v = st v).
  Proof.
    intros dz dl prefix suffix st result steps Hfresh Hrun.
    apply shifted_macro_in_context_no_shadow.
    - apply shift_no_shadow; exact Hfresh.
    - exact Hrun.
  Qed.
End StringMacroProperties.

(** Transfere o contrato fornecido pela macro para sua execução em contexto.
    Os lemas estruturais continuam disponíveis neste mesmo módulo. *)
Module StringMacroSpecProperties (M : TStringMacroWithSpec).
  Include StringMacroProperties M.

  (** A macro isolada e a macro em contexto produzem o mesmo estado final.
      A contagem de passos termina antes de executar o sufixo. *)
  Theorem correct_in_context : forall prefix suffix initial,
    (forall l, has_labeled_instr M.program l = true ->
      has_labeled_instr prefix l = false) ->
    M.precondition initial ->
    exists steps final,
      StringLang.compute_program (prefix ++ M.program ++ suffix)
        (StringLang.SNAP (length prefix) initial) steps =
        StringLang.SNAP (length prefix + length M.program) final /\
      M.postcondition (M.input_values initial) (final (Z M.z_shift)).
  Proof.
    intros prefix suffix initial Hshadow Hpre.
    destruct (M.execution_correct initial Hpre)
      as [steps [final [Hrun Hpost]]].
    destruct (macro_in_context M.program M.internal_jumps prefix suffix
      Hshadow initial final steps Hrun) as [used [Hused Hcontext]].
    exists used, final. split; assumption.
  Qed.

  (** A pré-condição é verificada nos nomes deslocados por dz. A saída
      satisfaz o contrato, e todas as variáveis fora da macro são preservadas. *)
  Theorem shifted_correct_in_context : forall dz dl prefix suffix initial,
    get_max_label prefix < dl + M.l_shift ->
    M.precondition (unshift_state dz initial) ->
    exists steps final,
      StringLang.compute_program (prefix ++ shift dz dl ++ suffix)
        (StringLang.SNAP (length prefix) initial) steps =
        StringLang.SNAP (length prefix + length M.program) final /\
      M.postcondition (M.input_values (unshift_state dz initial))
        (final (Z (dz + M.z_shift))) /\
      (forall v, outside dz v -> final v = initial v).
  Proof.
    intros dz dl prefix suffix initial Hfresh Hpre.
    destruct (M.execution_correct (unshift_state dz initial) Hpre)
      as [steps [result [Hrun Hpost]]].
    destruct (shifted_macro_in_context dz dl prefix suffix initial result steps
      Hfresh Hrun) as [used [final [Hused [Hcontext [Hstate Houtside]]]]].
    exists used, final. split; [exact Hcontext|]. split; [|exact Houtside].
    change (M.postcondition (M.input_values (unshift_state dz initial))
      (final (shift_variable dz (Z M.z_shift)))).
    rewrite (Hstate (Z M.z_shift)). exact Hpost.
  Qed.
End StringMacroSpecProperties.
