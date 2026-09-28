From Triq Require NatLang.
From Triq Require Import LanguagesCommon.

From Stdlib Require Import Nat.
From Stdlib Require Import List.
From Stdlib Require Extraction.
From Stdlib Require Import Lia.
Import ListNotations.

(** ** Obtendo a Maior Variável Z em p_nat *)

Fixpoint get_max_z (l : NatLang.program) : nat :=
    match l with
    | [] => 0
    | NatLang.Instr opt_lbl (NatLang.INCR (Z n))  :: t 
    | NatLang.Instr opt_lbl (NatLang.DECR (Z n))  :: t 
    | NatLang.Instr opt_lbl (NatLang.IF_GOTO (Z n) _ )  :: t  =>
      Nat.max n (get_max_z t) 
    | _ :: t => get_max_z t
    end.


(** ** Obtendo a Maior Label em p_nat *)


Fixpoint get_max_label (l : NatLang.program) : nat :=
  match l with
  | [] => 0
  | NatLang.Instr opt_lbl (NatLang.IF_GOTO _ (A goto_idx)) :: t =>
      match opt_lbl with
      | None => Nat.max goto_idx (get_max_label t)
      | Some (A n) => Nat.max goto_idx (Nat.max n (get_max_label t))
      end
  | NatLang.Instr opt_lbl _ :: t =>
      match opt_lbl with
      | None => get_max_label t
      | Some (A n) => Nat.max n (get_max_label t)
      end
  end.


(** * Label Pertence a Alguma Instrução em p_nat à Esquerda *)

Fixpoint has_labeled_instr p_nat (lbl : label)  :=
  match p_nat with
  | [] => false
  | NatLang.Instr opt_lbl _ :: t => match opt_lbl with 
                                       | Some lbl' => if eqb_lbl lbl lbl'
                                                      then true
                                                      else has_labeled_instr t lbl
                                       | None => has_labeled_instr t lbl
                                       end
  end.

Definition var_in_instr (i : NatLang.instruction) 
  (var : variable) :=
  match i with 
  | NatLang.Instr _ (NatLang.INCR x)
  | NatLang.Instr _ (NatLang.DECR x)
  | NatLang.Instr _ (NatLang.IF_GOTO x _) =>  var = x
  end.

Fixpoint var_in_program (p : NatLang.program) (var : variable) :=
  match p with 
  | h :: t => (var_in_instr h var) \/ var_in_program t var
  | [] => False
  end.


Lemma get_max_label_cons : forall h t, 
  NatUtils.get_max_label (h :: t) >= NatUtils.get_max_label t.
Proof.
  intros. simpl. destruct h. destruct s.
  + destruct o.
    ++ destruct l. lia.
    ++ lia.
  + destruct o.
    ++ destruct l. lia.
    ++ lia.
  + destruct l.
    destruct o.
    ++ destruct l; lia.
    ++ lia.
Qed.

Lemma goto_label_ge_max_label : forall p_nat i x instr_label goto_idx,
  nth_error p_nat i = Some (NatLang.Instr instr_label
  (NatLang.IF_GOTO x (A goto_idx))) ->
  NatUtils.get_max_label p_nat >= goto_idx.
Proof.
  induction p_nat as [|h t]; intros.
  - rewrite nth_error_nil in H. discriminate.
  - destruct i.
    + simpl. simpl in H. injection H as h_eq.
      rewrite h_eq. destruct instr_label.
      ++ destruct l. lia.
      ++ lia.
    + simpl in H. assert (NatUtils.get_max_label t >= goto_idx).
      { apply IHt with i x instr_label, H. }
      enough (NatUtils.get_max_label (h :: t) >= NatUtils.get_max_label t).
      lia. apply get_max_label_cons.
Qed.


Lemma nat_instr_le_max_label : forall p_nat instr_label,
  NatUtils.has_labeled_instr p_nat instr_label = true ->
  label_le_idx (Some instr_label) (NatUtils.get_max_label p_nat).
Proof.
  intros. induction p_nat.
  - simpl in H. discriminate.
  - simpl in *. destruct instr_label eqn:E; auto. destruct a.
    destruct s.
    + destruct o; auto.
      destruct l. simpl in *. destruct (n =? n0) eqn:E1. 
      ++ rewrite PeanoNat.Nat.eqb_eq in E1. rewrite E1.
          lia.
      ++ pose proof (IHp_nat H). lia.
    + destruct o; auto.
      destruct l. simpl in *. destruct (n =? n0) eqn:E1. 
      ++ rewrite PeanoNat.Nat.eqb_eq in E1. lia.
      ++ pose proof (IHp_nat H). lia.
    + destruct o; destruct l; auto. 
      ++ destruct l0. simpl in H. destruct (n =? n1) eqn:E1.
         * rewrite PeanoNat.Nat.eqb_eq in E1. lia.
         * pose proof (IHp_nat H). lia.
      ++ pose proof (IHp_nat H). lia.
Qed.

Lemma var_in_le_max : forall p_nat idx, 
  NatUtils.var_in_program p_nat (Z idx) ->
  idx <= NatUtils.get_max_z p_nat.
Proof.
  induction p_nat; intros.
  - simpl in H. destruct H.
  - simpl in *. destruct H. 
    + destruct a. destruct s. 
      ++ destruct v; try discriminate H.
         simpl in H. injection H as H. lia.
      ++ destruct v; try discriminate H.
         simpl in H. injection H as H. lia.
      ++ destruct v; try discriminate H.
         simpl in H. injection H as H. lia.
    + pose proof (IHp_nat idx H).
      destruct a. destruct s; destruct v; try lia.
Qed.


Lemma nth_error_implies_var_in : forall p_nat pos instr var,
  nth_error p_nat pos = Some (instr) ->
  NatUtils.var_in_instr instr var ->
  NatUtils.var_in_program p_nat var.
Proof.
  induction p_nat; intros.
  - rewrite nth_error_nil in H; discriminate.
  - destruct pos.
    + injection H as H. simpl. left. rewrite H. auto.
    + simpl in *. right. eauto.
Qed.
      

Lemma nth_error_implies_label_in : forall p_nat
  instr_label pos instr,
  nth_error p_nat pos = Some (NatLang.Instr (Some instr_label) instr) ->
  NatUtils.has_labeled_instr p_nat instr_label = true.
Proof.
  induction p_nat; intros.
  - rewrite nth_error_nil in H; discriminate.
  - destruct pos.
    + simpl in *. destruct a. destruct o eqn:E.
      ++ injection H as H. rewrite H, eqb_lbl_refl. reflexivity.
      ++ injection H as H. discriminate.
    + simpl in *. destruct a. destruct o eqn:E.
      ++ destruct (eqb_lbl instr_label l) eqn:E1; eauto.
      ++ eauto.
Qed.