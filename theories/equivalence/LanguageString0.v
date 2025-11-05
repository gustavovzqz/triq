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

Fixpoint get_str_prg_plain (nat_prg : NatLang.program) 
                          : StringLang.program 0 :=
  match nat_prg with
  | [] => []
  | i_nat :: rest =>
      (get_str_macro0 i_nat) ++ (get_str_prg_plain rest)
  end.

Definition equiv_pos 
  (p_nat : NatLang.program)
  (n : nat)
  (p_str : StringLang.program 0)
  (n' : nat) :=
  let nth_program_str := skipn n' p_str in
  match nth_error p_nat n with
  | None => nth_error p_str n' = None 
  | Some h => exists t_prog,
              nth_program_str = (get_str_macro0 h) ++ t_prog
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

Definition prog_equiv
  (p_nat : NatLang.program)
  (snap_nat : NatLang.snapshot)
  (p_str : StringLang.program 0)
  (snap_str : StringLang.snapshot 0) :=

  match snap_nat with
  | NatLang.SNAP n state_nat => 

  match snap_str with 
  | StringLang.SNAP n' state_str =>
  state_equiv state_nat state_str /\ 
  equiv_pos p_nat n p_str n'

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
  prog_equiv p_nat
             (NatLang.compute_program p_nat (NatLang.SNAP 0 state_nat) n)
             p_str
             (StringLang.compute_program p_str (StringLang.SNAP 0 state_str) n').
Proof.
   intros p_nat state_nat. exists (get_str_prg_plain p_nat).
   exists (get_equiv_state state_nat). induction n.
   + admit.
   + destruct IHn. unfold prog_equiv in H.
     destruct (NatLang.compute_program p_nat (NatLang.SNAP 0 state_nat)).
     destruct (StringLang.compute_program (get_str_prg_plain p_nat)
      (StringLang.SNAP 0 (get_equiv_state state_nat)) x) eqn:E.
      destruct H. unfold equiv_pos in H0.
      unfold NatLang.compute_program. 
      (* Intuição
         1. Preciso mostrar que compute_program (S n) initial_snap prg
         é o mesmo que compute_program 1 (compute_program n initial_snap prg) prg).
      ++ admit.
      ++ admit.


  (* rev_ind *)


