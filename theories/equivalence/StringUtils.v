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



Fixpoint label_in_instr p_str (lbl : label)  :=
  match p_str with
  | [] => false
  | StringLang.Instr opt_lbl _ :: t => match opt_lbl with 
                                       | Some lbl' => if eqb_lbl lbl lbl'
                                                      then true
                                                      else label_in_instr t lbl
                                       | None => label_in_instr t lbl
                                       end
  end.
