From Triq Require StringLang.
From Triq Require Import LanguagesCommon.
From Triq Require Import StringMacros.


From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith Lia.

Import ListNotations.

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



Ltac cancel_nat_goal :=
  (* Reassocia os parênteses da meta para a esquerda *)
  repeat rewrite <- Nat.add_assoc;
  repeat match goal with
  (* Caso 1: Com conteúdo no meio *)
  | [ |- context[ (?a + ?x) - ?a ] ] => replace ((a + x) - a) with x by lia
  (* Caso 2: Sem conteúdo no meio (vazio) *)
  | [ |- context[ ?a - ?a ] ] => replace (a - a) with 0 by lia
  end.

Ltac solve_var_equation :=
  (* 1. Expande as definições desejadas *)
  try unfold StringLang.append, StringLang.del, StringLang.update;
  
  (* 2. Simplifica as expressões booleanas *)
  repeat match goal with
  (* Caso Reflexivo: eqb_var x x vira true *)
  | [ |- context[ eqb_var ?x ?x ] ] =>
      rewrite (eqb_var_refl x)

  (* Ordem Direta: substitui exatamente a hipótese *)
  | [ H : ?b = false |- context[ ?b ] ] => rewrite H
  | [ H : ?b = true  |- context[ ?b ] ] => rewrite H

  (* Ordem Invertida: aplica simetria e reescreve *)
  | [ H : eqb_var ?x ?y = _ |- context[ eqb_var ?y ?x ] ] =>
      rewrite (eqb_var_symm y x); rewrite H
  end;

  (* 3. Tenta fechar o objetivo se ele já for reflexivo *)
  try reflexivity.


Ltac solve_label_diff :=
  solve [ eapply StringUtils.labels_greater_implies_diff; eauto; try lia ]
  ||
  solve [ eapply StringUtils.labels_less_implies_diff; eauto; try lia ]
  ||
  solve [ eapply labeled_instr_if_macro_false; eauto; try lia ].

Ltac clean_nat_eqb :=
  repeat match goal with
  (* 1. Caso Reflexivo rápido: substitui sem chamar o lia *)
  | [ |- context[ ?x =? ?x ] ] =>
      rewrite PeanoNat.Nat.eqb_refl

  (* 2. Tenta provar que é TRUE *)
  | [ |- context[ ?x =? ?y ] ] =>
      replace (x =? y) with true by (symmetry; apply PeanoNat.Nat.eqb_eq; lia)

  (* 3. Tenta provar que é FALSE *)
  | [ |- context[ ?x =? ?y ] ] =>
      replace (x =? y) with false by (symmetry; apply PeanoNat.Nat.eqb_neq; lia)
  end.


Ltac rewrite_labeled_instr_app :=
  match goal with
  | [ |- context[ StringLang.get_labeled_instr ?x ?y ] ] =>
      rewrite (StringUtils.get_labeled_instr_app) by solve_label_diff
  end.


Ltac rewrite_labeled_instr_app' :=
  match goal with
  | [ |- context[ StringLang.get_labeled_instr ?x ?y ] ] =>
      rewrite (StringUtils.get_labeled_instr_app); try solve_label_diff
  end.

Ltac progress_step :=
  try (clean_nat_eqb);
  repeat rewrite <- app_assoc;
  try (rewrite_labeled_instr_app);
  try rewrite nth_error_app2 by lia;
  cancel_nat_goal; simpl.
