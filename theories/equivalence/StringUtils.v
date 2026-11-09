From Triq Require StringLang.
From Triq Require Import LanguagesCommon.

From Stdlib Require Import Nat.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.


Fixpoint get_max_label (l : StringLang.program) : nat :=
  match l with
  | [] => 0
  | StringLang.Instr opt_lbl _ :: t =>
      match opt_lbl with
      | None => get_max_label t
      | Some (A n) => Nat.max n (get_max_label t)
      end
  end.



Fixpoint has_labeled_instr p_str (lbl : label)  :=
  match p_str with
  | [] => false
  | StringLang.Instr opt_lbl _ :: t => match opt_lbl with 
                                       | Some lbl' => if eqb_lbl lbl lbl'
                                                      then true
                                                      else has_labeled_instr t lbl
                                       | None => has_labeled_instr t lbl
                                       end
  end.

Lemma has_labeled_instr_app :
  forall l1 l2 lbl,
  StringUtils.has_labeled_instr l1 lbl = false ->
  StringUtils.has_labeled_instr (l1 ++ l2) lbl =
  StringUtils.has_labeled_instr l2 lbl.
Proof.
  induction l1; intros. 
  - reflexivity.
  - simpl. destruct a, o; auto.
    simpl in H. destruct (eqb_lbl lbl l); try discriminate; auto.
Qed.

Fixpoint labels_greater_than p_str value :=
  match p_str with
  | [] => True
  | StringLang.Instr opt_lbl _ :: t => match opt_lbl with 
                                       | Some (A n) => n > value 
                                                       /\
                                                       labels_greater_than t value
                                       | None => labels_greater_than t value 
                                       end
  end.

Fixpoint labels_less_than p_str value :=
  match p_str with
  | [] => True
  | StringLang.Instr opt_lbl _ :: t => match opt_lbl with 
                                       | Some (A n) => n < value 
                                                       /\
                                                       labels_less_than t value
                                       | None => labels_less_than t value 
                                       end
  end.


Lemma labels_greater_implies_diff :
  forall p_str n value,
  labels_greater_than p_str value ->
  n <= value ->
  has_labeled_instr p_str (A n) = false.
Proof.
  induction p_str; intros.
  + reflexivity.
  + simpl. simpl in H. destruct a, o.
    ++ destruct l. assert (n =? n0 = false).
       { rewrite PeanoNat.Nat.eqb_neq. lia. }
       rewrite H1. eapply IHp_str; eauto. 
       destruct H. auto.
    ++ eapply IHp_str; eauto.
Qed.

Lemma labels_less_implies_diff :
  forall p_str n value,
  labels_less_than p_str value ->
  n >= value ->
  has_labeled_instr p_str (A n) = false.
Proof.
  induction p_str; intros.
  + reflexivity.
  + simpl. simpl in H. destruct a, o.
    ++ destruct l. assert (n =? n0 = false).
       { rewrite PeanoNat.Nat.eqb_neq. lia. }
       rewrite H1. eapply IHp_str; eauto. 
       destruct H. auto.
    ++ eapply IHp_str; eauto.
Qed.


Lemma labels_greater_than_app :
  forall h t value,
  labels_greater_than h value ->
  labels_greater_than t value ->
  labels_greater_than (h ++ t) value.
Proof.
  induction h; intros; auto.
  simpl in *. destruct a. destruct o; auto.
  destruct l. destruct H. split; auto.
Qed.

Lemma labels_less_than_app :
  forall h t value,
  labels_less_than h value ->
  labels_less_than t value ->
  labels_less_than (h ++ t) value.
Proof.
  induction h; intros; auto.
  simpl in *. destruct a. destruct o; auto.
  destruct l. destruct H. split; auto.
Qed.


Lemma labels_leq_max : forall h n,
  n > get_max_label h ->
  labels_less_than h n.
Proof.
  induction h; intros.
  + simpl. apply I.
  + simpl. destruct a, o; auto.
    destruct l. split.
    ++ simpl in H. lia.
    ++ apply IHh. simpl in H. lia.
Qed.


Lemma labels_greater_than_S :
  forall p_str value,
  labels_greater_than p_str (S value) ->
  labels_greater_than p_str value.
Proof.
  induction p_str; intros; auto.
  simpl. destruct a, o; auto.
  destruct l. simpl in H. destruct H. split; auto.
  lia.
Qed.

Lemma get_labeled_instr_app :
  forall l1 l2 lbl,
  has_labeled_instr l1 lbl = false ->
  StringLang.get_labeled_instr (l1 ++ l2) lbl
  =
  length l1 + StringLang.get_labeled_instr l2 lbl.
Proof.
  induction l1; intros.
  - simpl. reflexivity.
  - simpl. simpl in H. destruct a eqn:E1. simpl.
    destruct o.
    + simpl. rewrite eqb_lbl_symm.
      destruct (eqb_lbl lbl l).
      ++ discriminate H. 
      ++ f_equal. auto.
    + simpl. f_equal; auto.
Qed.


(** Uma label presente é encontrada antes do fim do programa; acrescentar
    instruções à direita não muda sua primeira ocorrência. *)
Lemma get_labeled_instr_present : forall p lbl,
  has_labeled_instr p lbl = true ->
  StringLang.get_labeled_instr p lbl < length p.
Proof.
  induction p as [|[o s] p IH]; intros lbl H; simpl in *; try discriminate.
  destruct o as [l|]; simpl in *.
  - rewrite eqb_lbl_symm.
    destruct (eqb_lbl lbl l); simpl in *; auto with arith.
  - specialize (IH lbl H). lia.
Qed.

Lemma get_labeled_instr_app_present : forall p q lbl,
  has_labeled_instr p lbl = true ->
  StringLang.get_labeled_instr (p ++ q) lbl = StringLang.get_labeled_instr p lbl.
Proof.
  induction p as [|[o s] p IH]; intros q lbl H; simpl in *; try discriminate.
  destruct o as [l|]; simpl in *.
  - rewrite eqb_lbl_symm.
    destruct (eqb_lbl lbl l); simpl in *; auto.
  - f_equal. auto.
Qed.

(** SHIFT desloca os nomes locais, sem alterar os parâmetros X e Y. *)
Definition shift_variable dz v :=
  match v with Z k => Z (dz + k) | _ => v end.

Definition shift_label dl l := match l with A k => A (dl + k) end.

Definition shift_instruction dz dl i :=
  match i with
  | StringLang.Instr o s => StringLang.Instr (option_map (shift_label dl) o)
      (match s with
       | StringLang.APPEND c v => StringLang.APPEND c (shift_variable dz v)
       | StringLang.DEL v => StringLang.DEL (shift_variable dz v)
       | StringLang.IF_ENDS_GOTO v c l =>
           StringLang.IF_ENDS_GOTO (shift_variable dz v) c (shift_label dl l)
       end)
  end.

Definition shift_program dz dl (p : StringLang.program) :=
  map (shift_instruction dz dl) p.

Lemma shift_variable_eqb : forall dz v w,
  eqb_var (shift_variable dz v) (shift_variable dz w) = eqb_var v w.
Proof.
  intros dz v w; destruct v; destruct w; simpl; auto.
  destruct (Nat.eqb n n0) eqn:E.
  - apply PeanoNat.Nat.eqb_eq in E. subst; apply PeanoNat.Nat.eqb_refl.
  - apply PeanoNat.Nat.eqb_neq in E. apply PeanoNat.Nat.eqb_neq; lia.
Qed.

Lemma shift_label_eqb : forall dl l k,
  eqb_lbl (shift_label dl l) (shift_label dl k) = eqb_lbl l k.
Proof. intros dl [l] [k]; change (eqb_var (shift_variable dl (Z l))
  (shift_variable dl (Z k)) = eqb_var (Z l) (Z k)); apply shift_variable_eqb. Qed.

Lemma shift_length : forall p dz dl, length (shift_program dz dl p) = length p.
Proof. intros; apply length_map. Qed.

Lemma shift_nth_error : forall p dz dl pc,
  nth_error (shift_program dz dl p) pc = option_map (shift_instruction dz dl) (nth_error p pc).
Proof. intros; apply nth_error_map. Qed.

Lemma shift_has_label : forall p dz dl l,
  has_labeled_instr (shift_program dz dl p) (shift_label dl l) = has_labeled_instr p l.
Proof.
  induction p as [|[o s] p IH]; intros; simpl; auto.
  destruct o; simpl; auto. rewrite shift_label_eqb.
  destruct (eqb_lbl l l0); auto.
Qed.

Lemma shift_label_position : forall p dz dl l,
  StringLang.get_labeled_instr (shift_program dz dl p) (shift_label dl l) =
  StringLang.get_labeled_instr p l.
Proof.
  induction p as [|[o s] p IH]; intros; simpl; auto.
  destruct o; simpl; auto. rewrite shift_label_eqb.
  destruct (eqb_lbl l0 l); auto.
Qed.

Lemma nth_error_in_context : forall (prefix macro suffix : StringLang.program) pc,
  pc < length macro ->
  nth_error (prefix ++ macro ++ suffix) (length prefix + pc) = nth_error macro pc.
Proof.
  intros. rewrite nth_error_app2 by lia.
  replace (length prefix + pc - length prefix) with pc by lia.
  apply nth_error_app1; auto.
Qed.

Definition statement_variable (s : StringLang.statement) :=
  match s with
  | StringLang.APPEND _ v | StringLang.DEL v | StringLang.IF_ENDS_GOTO v _ _ => v
  end.

Lemma has_labeled_instr_in : forall p l,
  has_labeled_instr p l = true ->
  exists s, In (StringLang.Instr (Some l) s) p.
Proof.
  induction p as [|[o s] p IH]; intros l H; simpl in H; try discriminate.
  destruct o as [k|].
  - destruct (eqb_lbl l k) eqn:E.
    + apply lbl_eqb_eq in E. subst. exists s; left; reflexivity.
    + destruct (IH l H) as [t Hin]. exists t; right; exact Hin.
  - destruct (IH l H) as [t Hin]. exists t; right; exact Hin.
Qed.
