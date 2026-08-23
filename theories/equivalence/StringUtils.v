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
