From Stdlib Require Import List.
From Triq Require Import LanguagesCommon StringUtils StringMacros.
From Triq.string_lang Require StringLang.
Import ListNotations.

(** Esboço da expansão: preparação das entradas, seguida da macro deslocada.
    A preparação será construída com programas de atribuição e de limpeza.
    TODO: integrar a transferência de TransferMacroProperties depois de
    garantir que a atribuição preserve a origem e as demais variáveis externas. *)
Module StringMacroExpansion (M : TStringMacroWithSpec).
  Module Properties := StringMacroSpecProperties M.

  (** Espaço de rótulos reservado para o programa de preparação.
      TODO: definir a quantidade e garantir que seus rótulos estejam no
      intervalo [dl, dl + initialization_labels). *)
  Parameter initialization_labels : nat.

  (** TODO: copiar os argumentos para as entradas locais e zerar a saída
      e as auxiliares. Este é um programa, sem exigir a interface de macro. *)
  Parameter initialize : nat -> nat -> list variable -> StringLang.program.

  (** Os argumentos ficam fora do espaço de trabalho reservado para a macro. *)
  Definition valid_arguments dz (arguments : list variable) : Prop :=
    length arguments = M.n_input /\
    Forall (Properties.outside dz) arguments.

  (** Os rótulos da macro começam depois dos reservados para a preparação. *)
  Definition expand dz dl arguments : StringLang.program :=
    initialize dz dl arguments ++
    Properties.shift dz (dl + initialization_labels).

  (** A preparação estabelece a pré-condição, carrega os valores iniciais
      dos argumentos e preserva todas as variáveis externas.
      state_over delimita o alfabeto que o programa de transferência tratará;
      nenhuma variável é exigida vazia no estado inicial. *)
  Lemma initialization_correct_in_context :
    forall dz dl arguments prefix suffix initial,
    valid_arguments dz arguments ->
    StringLang.state_over initial M.max_char ->
    get_max_label prefix < dl ->
    exists steps prepared,
      StringLang.compute_program
        (prefix ++ initialize dz dl arguments ++ suffix)
        (StringLang.SNAP (length prefix) initial) steps =
        StringLang.SNAP
          (length prefix + length (initialize dz dl arguments)) prepared /\
      M.precondition (unshift_state dz prepared) /\
      M.input_values (unshift_state dz prepared) = map initial arguments /\
      (forall v, Properties.outside dz v -> prepared v = initial v).
  Proof.
    (* TODO: provar após definir os programas de atribuição e de limpeza. *)
  Admitted.

  (** Mesmo contrato da macro em contexto, com as entradas dadas pelos
      argumentos da chamada. A própria expansão garante a pré-condição. *)
  Theorem expansion_correct_in_context :
    forall dz dl arguments prefix suffix initial,
    valid_arguments dz arguments ->
    StringLang.state_over initial M.max_char ->
    get_max_label prefix < dl ->
    exists steps final,
      StringLang.compute_program (prefix ++ expand dz dl arguments ++ suffix)
        (StringLang.SNAP (length prefix) initial) steps =
        StringLang.SNAP
          (length prefix + length (expand dz dl arguments)) final /\
      M.postcondition (map initial arguments)
        (final (Z (dz + M.z_shift))) /\
      (forall v, Properties.outside dz v -> final v = initial v).
  Proof.
    (* TODO:
       1. Aplicar initialization_correct_in_context com o corpo no sufixo.
       2. Usar a reserva de rótulos para justificar o deslocamento do corpo.
       3. Aplicar Properties.shifted_correct_in_context ao estado preparado.
       4. Compor as execuções e as garantias de preservação. *)
  Admitted.
End StringMacroExpansion.
