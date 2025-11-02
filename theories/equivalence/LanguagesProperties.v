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

Inductive simulated_by {k : nat} : NatLang.program -> StringLang.program k -> Prop :=
  | Simulated_Instr :
      forall (i_nat : NatLang.instruction),
        simulated_by [i_nat] (get_str_macro k i_nat)
  | Simulated_App :
      forall h_nat t_nat (h_str t_str : StringLang.program k),
        simulated_by h_nat h_str ->
        simulated_by t_nat t_str ->
        simulated_by (h_nat ++ t_nat) (h_str ++ t_str).


(* Se retorna algo em p_nat, retorna o mesmo em p_str (em string)) *)

Definition state_equiv {k} (s_nat : NatLang.state) (s_str : StringLang.state k) :=
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

Definition snap_equiv {k} (p_nat : NatLang.program) (snap_nat : NatLang.snapshot)
  (p_str : StringLang.program k) (snap_str : StringLang.snapshot k) :=
  match snap_nat with
  | NatLang.SNAP n state_nat => 
  (**)
  match snap_str with 
  | StringLang.SNAP n' state_str =>
  state_equiv state_nat state_str /\ True
  (* Adicionar segunda parte da equivalência *)
  end
  (**)
  end.


Theorem nat_implies_string : forall {k : nat} (p_nat : NatLang.program)
  (initial_snap_nat : NatLang.snapshot), exists (p_str : StringLang.program k)
  (initial_snap_str : StringLang.snapshot k), forall (n : nat),
  exists (n' : nat),
  snap_equiv p_nat (NatLang.compute_program p_nat initial_snap_nat n)
             p_str (StringLang.compute_program p_str initial_snap_str n').
Proof.
  intros k. intros p_nat initial_snap_nat. exists [].
  exists (StringLang.SNAP 0 (StringLang.empty k)). induction n.
  + (* Caso n = 0 é trivial. Em zero passos p_str é equivalente. *) admit.
  + admit.

