From Triq Require StringLang.
From Triq Require Import LanguagesCommon.
From Triq Require Import StringMacros.


From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith Lia.

Import ListNotations.

Definition label_lt_idx l1 idx :=
  match l1 with
  | None => True 
  | Some (A k) => k < idx
  end.

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


Lemma labels_less_than_if : forall x if_idx max_char 
  goto_label label_idx,
  if_idx < label_idx ->

  StringUtils.labels_less_than (get_if_macro_label x 
  (Some (A if_idx)) max_char goto_label) label_idx.
Proof.
  intros.
  induction max_char.
  + simpl. lia.
  + simpl. split; try lia. auto.
Qed.

Lemma labels_less_than_incr_blocks : forall incr_idx x z aux max_char
  goto_label label_idx,
  incr_idx + max_char < label_idx -> 
  
  StringUtils.labels_less_than (get_all_incr_blocks x z aux 
  max_char incr_idx goto_label) label_idx.
Proof.
  intros. destruct max_char.
  + simpl. apply I.
  + simpl. induction max_char.
    - simpl. lia.
    - simpl. split; try lia. apply IHmax_char. lia.
Qed.

Lemma labels_less_than_di_blocks : forall di_idx x z aux max_char
  goto_label label_idx,
  di_idx + max_char < label_idx -> 
  
  StringUtils.labels_less_than (get_all_di_blocks x z aux 
  max_char di_idx goto_label) label_idx.
Proof.
  intros. destruct max_char.
  + simpl. lia.
  + simpl. induction max_char.
    - simpl. lia.
    - simpl. split; try lia. apply IHmax_char. lia.
Qed.

Lemma labels_less_than_instr : forall instr_label idx instr idx',
  label_lt_idx instr_label idx  ->
  idx' > idx ->
  StringUtils.labels_less_than 
  [StringLang.Instr instr_label instr] idx'.
Proof.
  intros. destruct instr_label.
  - destruct l. simpl in *. lia.
  - simpl. apply I.
Qed.

Lemma labels_less_than_transfer: forall label_idx x z 
instr_idx instr_idx' E aux max_char,
  instr_idx  < label_idx ->
  instr_idx' + max_char < label_idx ->
  StringUtils.labels_less_than (transfer_block (A instr_idx) x z 
  instr_idx' E aux max_char) label_idx.
Proof.
  intros. unfold transfer_block. 
  apply StringUtils.labels_less_than_app.
  apply labels_less_than_if; lia.
  simpl. apply labels_less_than_di_blocks. lia.
Qed.




Lemma labels_less_implies_diff_weak :
 forall (p_str : list StringLang.instruction) (n : nat),
       StringUtils.labels_less_than p_str n ->
        StringUtils.has_labeled_instr p_str (A n) = false.
Proof.
  intros.
  eapply StringUtils.labels_less_implies_diff.
  eauto. lia.
Qed.

Lemma get_labeled_instr_transfer: forall instr_label x z label_idx 
E aux max_char t,
  ((StringLang.get_labeled_instr ((transfer_block instr_label x z label_idx E
   aux max_char) ++ t)) instr_label) = 0.
Proof.
  intros. destruct max_char; simpl; rewrite eqb_lbl_refl; reflexivity.
Qed.

Ltac solve_less_than :=
  solve [apply StringUtils.labels_leq_max; try lia]
  ||
  solve [simpl; try lia]
  ||
  solve [eapply labels_less_than_incr_blocks; eauto; try lia ]
  ||
  solve [eapply labels_less_than_di_blocks; eauto; try lia ]
  ||
  solve [apply labels_less_than_if; try lia ]
  ||
  solve [apply labels_less_than_transfer; try lia]
  ||
  solve [eapply labels_less_than_instr; eauto; try lia ].


Ltac solve_less_than_app :=
  try solve_less_than;
  repeat (rewrite <- app_assoc);
  try (apply (StringUtils.labels_less_than_app));
  try solve_less_than.

Ltac cancel_nat_goal :=
  repeat rewrite <- Nat.add_assoc;
  repeat match goal with
  | [ |- context[ (?a + ?x) - ?a ] ] => replace ((a + x) - a) with x by lia
  | [ |- context[ ?a - ?a ] ] => replace (a - a) with 0 by lia
  end.

Ltac solve_var_equation :=
  try unfold StringLang.append, StringLang.del, StringLang.update;
  repeat match goal with
  | [ |- context[ eqb_var ?x ?x ] ] => rewrite (eqb_var_refl x)
  | [ H : ?b = false |- context[ ?b ] ] => rewrite H
  | [ H : ?b = true  |- context[ ?b ] ] => rewrite H
  | [ H : eqb_var ?x ?y = _ |- context[ eqb_var ?y ?x ] ] =>
      rewrite (eqb_var_symm y x); rewrite H
  end;
  try reflexivity.



Ltac solve_label_diff :=
  solve [ eapply StringUtils.labels_greater_implies_diff; eauto; try lia ]
  ||
  solve [ eapply StringUtils.labels_less_implies_diff; eauto; try lia ]
  ||
  solve [ apply labels_less_implies_diff_weak; solve_less_than_app; try lia]
  ||
  solve [ eapply labeled_instr_if_macro_false; eauto; try lia ].

Ltac clean_nat_eqb :=
  repeat match goal with
  | [ |- context[ ?x =? ?x ] ] =>
      rewrite PeanoNat.Nat.eqb_refl
  | [ |- context[ ?x =? ?y ] ] => replace (x =? y) with true by 
        (symmetry; apply PeanoNat.Nat.eqb_eq; lia)
  | [ |- context[ ?x =? ?y ] ] => replace (x =? y) with false by 
      (symmetry; apply PeanoNat.Nat.eqb_neq; lia)
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
