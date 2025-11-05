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
Defined.

Definition get_incr_macro_0 opt_lbl x :=
  StringLang.Instr opt_lbl (StringLang.APPEND zero_prf x).


Definition get_decr_macro_0 opt_lbl x : (StringLang.instruction 0) :=
  StringLang.Instr opt_lbl (StringLang.DEL x).


Definition get_if_macro_0 opt_lbl x l :=
StringLang.Instr opt_lbl (StringLang.IF_ENDS_GOTO x zero_prf l).

Definition get_str_macro0 (i_nat : NatLang.instruction) :
  (StringLang.instruction 0 ) := 
  match i_nat with 
  | NatLang.Instr opt_lbl (NatLang.INCR x) => get_incr_macro_0 opt_lbl x
  | NatLang.Instr opt_lbl (NatLang.DECR x) =>  get_decr_macro_0 opt_lbl x
  | NatLang.Instr opt_lbl (NatLang.IF_GOTO x l) => get_if_macro_0 opt_lbl x l
  end.

Fixpoint get_str_prg (nat_prg : NatLang.program) 
                          : StringLang.program 0 :=
  match nat_prg with
  | [] => []
  | i_nat :: rest =>
      (get_str_macro0 i_nat) :: (get_str_prg rest)
  end.

Definition equiv_pos 
  (p_nat : NatLang.program)
  (n : nat)
  (p_str : StringLang.program 0)
  (n' : nat) :=
  match nth_error p_nat n with
  | None => nth_error p_str n' = None 
  | Some h => nth_error p_str n' = Some (get_str_macro0 h)
  end.


Inductive simulated_by : NatLang.program -> StringLang.program 0 -> Prop :=
  | Simulated_Empty :
      simulated_by [] []

  | Simulated_Instr :
      forall (i_nat : NatLang.instruction),
        simulated_by [i_nat] [(get_str_macro0 i_nat)]

  | Simulated_App :
      forall h_nat t_nat (h_str t_str : StringLang.program 0),
        simulated_by h_nat h_str ->
        simulated_by t_nat t_str ->
        simulated_by (h_nat ++ t_nat) (h_str ++ t_str).


(* Se retorna algo em p_nat, retorna o mesmo em p_str (em string)) *)

Definition state_equiv (s_nat : NatLang.state) (s_str : StringLang.state 0) :=
  (* Se s_nat x = v, então string_to_nat (s_str x) também retorna v *)
  forall (x : variable) (v : nat),
  s_nat x = v -> string_to_nat (s_str x) = v.

Definition prog_equiv
  (p_nat    : NatLang.program)
  (snap_nat : NatLang.snapshot)
  (p_str    : StringLang.program 0) 
  (snap_str : StringLang.snapshot 0) :=

  match snap_nat with
  | NatLang.SNAP n state_nat => (
      match snap_str with
      | StringLang.SNAP n' state_str =>
      state_equiv state_nat state_str  /\ equiv_pos p_nat n p_str n'
      end)
  end.
  

Definition get_equiv_state nat_state : (StringLang.state 0) :=
  (fun x => nat_to_string 0 (nat_state x)).


Lemma simulated_empty_left : forall h t,  simulated_by [] (h :: t)-> False.
Proof.
Admitted.

Lemma simulated_empty_right : forall h t,  simulated_by (h :: t) [] -> False.
Proof.
Admitted.


Lemma equiv_pos_simulated_0 : forall p_nat p_str, 
  simulated_by p_nat p_str -> equiv_pos p_nat 0 p_str 0.
Proof.
  intros p_nat p_str simulated_prf. unfold equiv_pos. 
  induction simulated_prf.
  + reflexivity.
  + reflexivity.
  + destruct h_nat; destruct h_str; destruct t_nat; destruct t_str; try (assumption).
    ++ exfalso. apply simulated_empty_left with i h_str. assumption.
    ++ exfalso. apply simulated_empty_left with i h_str. assumption.
    ++ exfalso. apply simulated_empty_right with i h_nat. assumption.
    ++ exfalso. apply simulated_empty_right with i h_nat. assumption.
Qed.

(** Teorema principal *)
Theorem nat_implies_string :
  forall (p_nat : NatLang.program)
         (state_nat : NatLang.state)
         (p_str : StringLang.program 0),
  simulated_by p_nat p_str ->

  exists (state_str : StringLang.state 0), 

  forall (n : nat),
  exists (n' : nat),
  prog_equiv p_nat
             (NatLang.compute_program p_nat (NatLang.SNAP 0 state_nat) n)
             p_str
             (StringLang.compute_program p_str (StringLang.SNAP 0 state_str) n').
Proof.
  intros p_nat state_nat p_str simulated_prf. exists (get_equiv_state state_nat).
  induction n.
    (* Caso Base:

       Para mostramos prog_equiv, precisamos mostrar 1) state_equiv e 2) equiv_pos. 

       1) Fazendo n' = 0, temos que em zero passos o programa retorna a própria snapshot.
       Assim, basta mostrar que (get_equiv_state state_nat) é equivalente a state_nat.

       2) Com n' = 0 e n = 0, a snapshot retornará (S, 0). Assim, precisamos mostrar que
       se nth_error 0 prg é alguma instrução, então o programa de strings possui a macro
       na posição n' (zero). O que é verdade pela hipótese simulated_prf.
     *)
  - exists 0. (* n' = 0 *)
    split. (* Dividir a prova em 1) e 2) *)
    + admit. (* Criar lemma dizendo que get_equiv_state funciona como o esperado *)
    + apply equiv_pos_simulated_0, simulated_prf. (* Completar lema, versão
                                                     funcional pode ajudar. *)


  (* Passo da Indução:
    Temos que existe um n' onde prog_equiv p_nat snap1 n
                                           p_str snap2 n'

     Precisamos saber qual a próxima instrução de n. Assim, vamos quebrar
     a snap1 e a snap2. *)
  - destruct IHn as [n']. (* Obtendo n' *)
    (* Vendo os valores da snap1 e snap2 *)
    destruct (NatLang.compute_program p_nat (NatLang.SNAP 0 state_nat) n)
    as [k S]. (* A próxima linha de p_nat é k *)
    destruct (StringLang.compute_program p_str (StringLang.SNAP 0 
    (get_equiv_state state_nat)) n') as [k' S']. (* A próxima linha de p_str
                                                    é k' *)
    destruct H. (* Quebramos a hipótese de indução em duas afirmações:
                   1) Os estados após a computação são equivalentes.
                   2) A próxima linha a ser executada em p_nat é ...
                      e em p_str é ... *)

    (* Para esse caso, o número de passos para o programa
       de strings sera S n' para o passo da indução,  mas, em
       casos genéricos, precisamos primeiro ver quem é a nth_error k de p_nat. *)

    unfold equiv_pos in H0. destruct (nth_error p_nat k) eqn:E. (* Quem é a instrução
                                                             da próxima linha
                                                             a ser executada? *)
    +  (* nth_error p_nat k = Some i*)

