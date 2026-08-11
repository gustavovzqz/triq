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


