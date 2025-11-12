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
  exists 0.  apply PeanoNat.Nat.le_0_l.
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
  forall (x : variable) (v : StringLang.string 0),
  nat_to_string 0 (s_nat x) = v -> s_str x = v.

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

Lemma app_not_nil : forall A (l1 : list A) l2, l1 ++ l2 <> [] ->
  l1 <> [] \/ l2 <> [].
Proof.
  intros A l1 l2 app. destruct l1; destruct l2.
  + simpl in app. exfalso. exact (app eq_refl).
  + right. intros H. discriminate H.
  + left. intros H. discriminate H.
  + right. intros H. discriminate H.
Qed.
 
Lemma simulated_empty_left_aux : forall p_nat p_str ,  (p_nat = []) ->
  (p_str <> []) ->
  simulated_by p_nat p_str -> False.  
Proof.
  intros p_nat p_str p_nat_zero p_str_zero sim. induction sim.
  + exact (p_str_zero eq_refl).
  + discriminate p_nat_zero.
  + apply app_eq_nil in p_nat_zero. destruct p_nat_zero.
    apply app_not_nil in p_str_zero. destruct p_str_zero.
    ++ apply IHsim1; assumption.
    ++ apply IHsim2; assumption.
Qed.

Theorem simulated_empty_left : forall h t,  simulated_by [] (h :: t)-> False.
Proof.
  intros h t sim. apply simulated_empty_left_aux with [] (h :: t).
  + reflexivity.
  + intros H; discriminate H.
  + assumption.
Qed.


Lemma simulated_empty_right_aux : forall p_nat p_str ,  (p_nat <> []) ->
  (p_str = []) ->
  simulated_by p_nat p_str -> False.  
Proof.
  intros p_nat p_str p_nat_zero p_str_zero sim. induction sim.
  + exact (p_nat_zero eq_refl).
  + discriminate p_str_zero.
  + apply app_eq_nil in p_str_zero. destruct p_str_zero.
    apply app_not_nil in p_nat_zero. destruct p_nat_zero.
    ++ apply IHsim1; assumption.
    ++ apply IHsim2; assumption.
Qed.

Lemma simulated_empty_right : forall h t,  simulated_by (h :: t) [] -> False.
Proof.
intros h t sim. apply simulated_empty_right_aux with  (h :: t) [].
  + intros H; discriminate H.
  + reflexivity.
  + assumption.
Qed.


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



Lemma get_equiv_state_correct : forall state_nat,
  state_equiv state_nat (get_equiv_state state_nat).
Proof.
  intros state_nat. unfold get_equiv_state. unfold state_equiv.
  intros x v state_x_eq_v. destruct (state_nat x) eqn:E.
  + simpl. rewrite <- state_x_eq_v. reflexivity.
  + rewrite <- state_x_eq_v. reflexivity.
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
    + apply get_equiv_state_correct. 
    + apply equiv_pos_simulated_0, simulated_prf. 


  (* Passo da Indução:
    Temos que existe um n' onde prog_equiv p_nat snap1 n
                                           p_str snap2 n'

     Precisamos saber qual a próxima instrução de n. Assim, vamos quebrar
     a snap1 e a snap2. *)
  - destruct IHn as [n']. (* Obtendo n' *)
    (* Vendo os valores da snap1 e snap2 *)
    destruct (NatLang.compute_program p_nat (NatLang.SNAP 0 state_nat) n)
    as [k s] eqn:snap_nat. (* A próxima linha de p_nat é k *)
    destruct (StringLang.compute_program p_str (StringLang.SNAP 0 
    (get_equiv_state state_nat)) n') as [k' s'] eqn:snap_str. 
    (* A próxima linha de p_str é k' *)
    destruct H. (* Quebramos a hipótese de indução em duas afirmações:
                   1) Os estados após a computação são equivalentes.
                   2) A próxima linha a ser executada em p_nat é ...
                      e em p_str é ... *)

    (* Para esse caso, o número de passos para o programa
       de strings sera S n' para o passo da indução,  mas, em
       casos genéricos, precisamos primeiro ver quem é a nth_error k de p_nat. *)

    unfold equiv_pos in H0. 
    destruct (nth_error p_nat k) eqn:E. (* Quem é a próxima instrução de nat? *)
    (* nth_error p_nat k = Some i *)
    (* Aqui, temos que nth_error p_str k' é Some (get_str_macro0 i).
       No caso genérico, a alternativa que pensei é a seguinte:
       1. skipn k' = [get_str_macro0 i] ++ algo, daí podemos
          derivar que nth_error k' + 1 ... Até o tamanho total da macro.

          Aqui está o lemma útil:

            nth_error_skipn:
              forall [A : Type] (n : nat) (l : list A) (i : nat),
              nth_error (skipn n l) i = nth_error l (n + i)  *)
    (* Qual a instrução e o statement? *)
    + destruct i as [opt_lbl statement]. destruct statement.
      (* x <- x + 1*)
      ++ exists (S n').
         (* Eu poderia colocar logo como `exists k' + num exec macro *)
         unfold prog_equiv. simpl. rewrite snap_nat.
         unfold NatLang.next_step. rewrite E. rewrite snap_str.
         unfold StringLang.next_step. rewrite H0. simpl.
         split.
         +++ unfold state_equiv. intros x v0.
             unfold StringLang.append.
             unfold NatLang.incr.
             unfold NatLang.update.
             unfold StringLang.update.
             admit.
         +++ admit.
             (* Um lemma auxiliar resolve. Provavelmente usando skipn
                é mais intuitivo *)
      (* x <- x - 1*)
      ++ exists (S (n')).
         unfold prog_equiv. simpl. rewrite snap_nat.
         unfold NatLang.next_step. rewrite E. rewrite snap_str.
         unfold StringLang.next_step. rewrite H0. simpl.
         split.
         +++ admit. (* Basta provar equivalência ... *)
         +++ admit. (* mesmo lema que o anterior *)
      (* if x != 0 goto l*)
      ++ exists (S (n')).
         unfold prog_equiv. simpl. rewrite snap_nat.
         unfold NatLang.next_step. rewrite E. rewrite snap_str.
         unfold StringLang.next_step. simpl in H0. rewrite H0. simpl.
         (* Essa parte está do IF está um pouco diferente. Na verdade,
            todas as partes anteriores estão simplificando as macros,
            e as equivalências pendentes estão nas instruções. Preciso
            adaptar a finalização da prova para ficar dependendo das 
            macros serem equivalentes , não as instruções finais *)
Abort.
           
