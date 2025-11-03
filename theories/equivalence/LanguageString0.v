From Triq Require NatLang.
From Triq Require NatLangProperties.
From Triq Require StringLang.
From Triq Require StringLangProperties.
From Triq Require Import LanguagesCommon.
From Triq Require Import LanguagesUtils.
From Coq Require Import Nat.
From Coq Require Import List.
From Coq Require Extraction.
From Coq Require Import Lia.
Import ListNotations.



(** O programa p_nat é simulado pelo prorgama p_str *)


Definition zero_prf : StringLang.alphabet 0.
Proof.
  exists 0. constructor.
Qed. 

Definition get_incr_macro_0 opt_lbl x :=
  [StringLang.Instr opt_lbl (StringLang.APPEND zero_prf x)].


Definition get_decr_macro_0 opt_lbl x : (StringLang.program 0) :=
  [StringLang.Instr opt_lbl (StringLang.DEL x)].


Definition get_if_macro_0 opt_lbl x l :=
  [StringLang.Instr opt_lbl (StringLang.IF_ENDS_GOTO x zero_prf l)].

Definition get_str_macro0 (i_nat : NatLang.instruction) :
  (StringLang.program 0 ) := 
  match i_nat with 
  | NatLang.Instr opt_lbl (NatLang.INCR x) => get_incr_macro_0 opt_lbl x
  | NatLang.Instr opt_lbl (NatLang.DECR x) =>  get_decr_macro_0 opt_lbl x
  | NatLang.Instr opt_lbl (NatLang.IF_GOTO x l) => get_if_macro_0 opt_lbl x l
  end.

Inductive simulated_by : NatLang.program -> StringLang.program 0 -> Prop :=
  | Simulated_Instr :
      forall (i_nat : NatLang.instruction),
        simulated_by [i_nat] (get_str_macro0 i_nat)
  | Simulated_Empty :
        simulated_by [] [] 
  | Simulated_App :
      forall h_nat t_nat (h_str t_str : StringLang.program 0),
        simulated_by h_nat h_str ->
        simulated_by t_nat t_str ->
        simulated_by (h_nat ++ t_nat) (h_str ++ t_str).

Definition get_str_prg nat_prg : {str_prg | simulated_by nat_prg str_prg}.
Proof.
  induction nat_prg.
  + exists []. apply Simulated_Empty.
  + destruct IHnat_prg as [str_prg equiv_nat_str]. 
    exists ((get_str_macro0 a) ++ str_prg).
    assert (a :: nat_prg = [a] ++ nat_prg) as cons_app_equiv by reflexivity.
    rewrite cons_app_equiv. apply Simulated_App.
    ++ apply Simulated_Instr.
    ++ assumption.
Defined.

Fixpoint get_str_prg_plain (nat_prg : NatLang.program) 
                          : StringLang.program 0 :=
  match nat_prg with
  | [] => []
  | i_nat :: rest =>
      (get_str_macro0 i_nat) ++ (get_str_prg_plain rest)
  end.


(* Se retorna algo em p_nat, retorna o mesmo em p_str (em string)) *)

Definition state_equiv (s_nat : NatLang.state) (s_str : StringLang.state 0) :=
  (* Se s_nat x = v, então string_to_nat (s_str x) também retorna v *)
  forall (x : variable) (v : nat),
  s_nat x = v -> string_to_nat (s_str x) = v.


(* Os programas p_nat e p_str são equivalentes em SNAPSHOT significa que:
    snapshot (S, i) de nat e (S', i') de str
    1. Os estados são equivalentes
    2. Se o programa da i-ésima instrução em diante em p_nat é (...),
                                              então o de str é (...):
    | [] => []
    | h_nat :: t_nat => (get_str_macro h) ++ t_str *)

Definition snap_equiv
  (snap_nat : NatLang.snapshot)
  (snap_str : StringLang.snapshot 0) :=

  match snap_nat with
  | NatLang.SNAP n state_nat => 

  match snap_str with 
  | StringLang.SNAP n' state_str =>
  state_equiv state_nat state_str 
  (* Adicionar segunda parte da equivalência *)
  end
  (**)
  end.


Definition get_equiv_state nat_state : (StringLang.state 0) :=
  (fun x => nat_to_string 0 (nat_state x)).




Theorem nat_implies_string : 
  forall (p_nat : NatLang.program)
         (state_nat : NatLang.state),
  exists (p_str : StringLang.program 0)
         (state_str : StringLang.state 0), 
  forall (n : nat),
  exists (n' : nat),
  snap_equiv (NatLang.compute_program p_nat (NatLang.SNAP 0 state_nat) n)
             (StringLang.compute_program p_str (StringLang.SNAP 0 state_str) n').
Proof.
   intros p_nat state_nat. exists (get_str_prg_plain p_nat).
   exists (get_equiv_state state_nat). intros n.
   induction p_nat using rev_ind.
   + admit.
   + destruct IHp_nat. exists n.


  (* rev_ind *)
