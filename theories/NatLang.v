(** * NatLang: Linguagem Simples Baseada em Naturais *)

From Stdlib Require Import Nat.
From Stdlib Require Import List.

Import ListNotations.

(** Elementos Básicos de um Programa *)

Inductive variable : Type :=
  | X : nat -> variable  (* input  *)
  | Z : nat -> variable  (* local  *)
  | Y : variable.        (* output *)

Inductive label : Type :=
  | A : nat -> label.

Inductive statement : Type :=
  | INCR : variable -> statement
  | DECR : variable -> statement
  | IF_GOTO   : variable -> option label -> statement
  | SKIP : variable -> statement.

Inductive instruction : Type :=
  | Instr : option label -> statement -> instruction.

Definition program := list instruction.

(** Notações. Adaptadas de: 
    https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html *)

Declare Custom Entry com.
Declare Scope nat_lang_scope.
Declare Custom Entry com_aux.

Notation "<{ e }>" := e (e custom com_aux) : nat_lang_scope.
Notation "e" := e (in custom com_aux at level 0, e custom com) : nat_lang_scope.
Notation "( x )" := x (in custom com, x at level 99) : nat_lang_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : nat_lang_scope.

Notation "x <- + 1" := (INCR x)
  (in custom com at level 50, left associativity).

Notation "x <- - 1" := (DECR x)
  (in custom com at level 50, left associativity).

Notation "x <- + 0" := (SKIP x)
  (in custom com at level 50, left associativity).


Notation "'IF' x 'GOTO' y " :=
         (IF_GOTO x y) 
           (in custom com at level 89, x at level 99,
            y at level 99) : nat_lang_scope.

Notation "[ l ] s " := (Instr (l) s)
  (at level 0, s custom com at level 200) : nat_lang_scope.

Notation "[ ] s " := (Instr None s)
  (at level 0, s custom com at level 200) : nat_lang_scope.


Notation "'[ i1 ; .. ; iN ]'" := (cons i1 .. (cons iN nil) ..)
  (at level 0, i1 custom com, iN custom com) : nat_lang_scope.

Open Scope nat_lang_scope.

(** Decidibilidade e Auxiliares Envolvendo Igualdades *)

Definition eqb_var v1 v2 := 
  match v1, v2 with 
  | X a, X b => a =? b
  | Z a, Z b => a =? b
  | Y, Y  => true
  | _, _ => false
  end.

Definition eqb_lbl l1 l2 :=
  match l1, l2 with 
  | A a, A b => a =? b
  end.

Theorem eqb_var_refl : forall v, eqb_var v v = true.
Proof.
  destruct v; try (apply PeanoNat.Nat.eqb_refl); reflexivity.
Qed.

Theorem var_eqb_eq : forall v1 v2 : variable, eqb_var v1 v2 = true <-> v1 = v2.
Proof.
  intros v1 v2. split; intros H.
  (* -> *) 
  destruct v1; destruct v2; (try discriminate).
  - simpl in H. rewrite PeanoNat.Nat.eqb_eq in H. rewrite H. reflexivity.
  - simpl in H. rewrite PeanoNat.Nat.eqb_eq in H. rewrite H. reflexivity.
  - reflexivity.
  (* <- *)
  - rewrite H. apply eqb_var_refl.
Qed.

Theorem var_eqb_neq : forall v1 v2 : variable, eqb_var v1 v2 = false <-> v1 <> v2.
Proof.
  intros v1 v2. split; intros H.
  - intros H1. rewrite H1 in H. rewrite eqb_var_refl in H. discriminate.
  - unfold not in H. destruct (eqb_var v1 v2) eqn:Heq.
    + apply var_eqb_eq in Heq. contradiction. 
    + reflexivity.
Qed.


Definition eq_inst_label (instr : instruction ) (opt_lbl : option label) :=
  match instr, opt_lbl with 
  | Instr (Some lbl_a) _, Some lbl_b => eqb_lbl lbl_a lbl_b
  | _, _                => false
  end.

(** Função para encontrar a posição da primeira instrução com certa label 
    em um programa *)

Definition get_labeled_instr (p : program) (lbl : option label) :=
  let fix aux l n :=
    match l with 
    | h :: t => match (eq_inst_label h lbl) with 
                | true => n
                | false => aux t (n + 1)
                end
    | []     => n 
    end
  in aux p 0.


(** Estado de um Programa *)

Definition state := variable -> nat.

Definition empty : state := (fun _ => 0).

Definition update (m : state ) (x : variable) (v : nat) :=
  fun x' => if eqb_var x x' then v else m x'.

Definition incr (m : state ) (x : variable) :=
  let v := m x in 
  update m x (v + 1).

Definition decr (m : state ) (x : variable) :=
  let v := m x in 
  update m x (v - 1).

Inductive snapshot :=
  | SNAP : nat -> state -> snapshot.

Definition initial_snapshot := SNAP 0 empty.

Definition create_state x :=
  update empty (X 0) x.


(** Propriedade de Passo de Pomputação:

    steps_to programa s s' :=
    O programa de snapshot s possui como próxima snapshot s' *)

Inductive steps_to : program -> snapshot -> snapshot -> Prop :=
  (* x <- x + 1 *)
  | S_Incr : forall program x i opt_lbl instruction st,
      nth_error program i = Some instruction ->
      instruction = <{[opt_lbl] x <- + 1}>    ->
      steps_to program (SNAP i st) (SNAP (i + 1) (incr st x))

  (* x <- x - 1 *)
  | S_Decr: forall program x i opt_lbl instruction st,
      nth_error program i = Some instruction ->
      instruction = <{[opt_lbl] x <- - 1}>  ->
      steps_to program (SNAP i st) (SNAP (i + 1) (decr st x))

  (* x <- x + 0 *)
  | S_Skip: forall program x i opt_lbl instruction st,
      nth_error program i = Some instruction ->
      instruction = <{[opt_lbl] x <- + 0}>   ->
      steps_to program (SNAP i st) (SNAP (i + 1) st)

  (* IF X != 0 GOTO l, x = 0 *)
  | S_If_0: forall program x i opt_lbl l instruction st,
      nth_error program i = Some instruction   ->
      st x = 0                                 ->
      instruction = <{[opt_lbl] IF x GOTO l }> ->
      steps_to program (SNAP i st) (SNAP (i + 1) st)

  (* IF X != 0 GOTO l, x != 0 *)
  | S_If_S: forall program x i j opt_lbl l instruction st,
      nth_error program i = Some instruction  ->
      st x <> 0                               ->
      instruction = <{[opt_lbl] IF x GOTO l}>  ->
      (get_labeled_instr program l = j) ->
      steps_to program (SNAP i st) (SNAP j st )

  (* Linha fora dos limites do programa *)
  | S_Out: forall program i st,
      nth_error program i = None ->
      steps_to program (SNAP i st) (SNAP i st).

Hint Constructors steps_to : stepdb.



(** Unicidade do Passo de Computação *)

Theorem step_unique : forall p snap1 snap2 snap3,
  steps_to p snap1 snap2 ->
  steps_to p snap1 snap3 ->
  snap2 = snap3.
Proof.
  intros. destruct snap1. inversion H.
  + inversion H0; subst.
    ++ rewrite H4 in H10. inversion H10. reflexivity.
    ++ rewrite H4 in H10. inversion H10. 
    ++ rewrite H4 in H10. inversion H10. 
    ++ rewrite H4 in H9.  inversion H9. 
    ++ rewrite H4 in H9.  inversion H9. 
    ++ rewrite H4 in H11. inversion H11. 
  + inversion H0; subst.
    ++ rewrite H4 in H10. inversion H10. 
    ++ rewrite H4 in H10. inversion H10. reflexivity.
    ++ rewrite H4 in H10. inversion H10. 
    ++ rewrite H4 in H9.  inversion H9. 
    ++ rewrite H4 in H9.  inversion H9. 
    ++ rewrite H4 in H11. inversion H11. 
  + inversion H0; subst.
    ++ rewrite H4 in H10. inversion H10. 
    ++ rewrite H4 in H10. inversion H10. 
    ++ rewrite H4 in H10. inversion H10. reflexivity.
    ++ rewrite H4 in H9.  inversion H9. 
    ++ rewrite H4 in H9.  inversion H9. 
    ++ rewrite H4 in H11. inversion H11. 
  + inversion H0; subst.
    ++ rewrite H3 in H11. inversion H11. 
    ++ rewrite H3 in H11. inversion H11. 
    ++ rewrite H3 in H11. inversion H11. 
    ++ rewrite H3 in H10. inversion H10. reflexivity.
    ++ rewrite H3 in H10. inversion H10. subst. apply H11 in H5. destruct H5.
    ++ rewrite H3 in H12. inversion H12.
  + inversion H0; subst.
    ++ rewrite H3 in H12. inversion H12. 
    ++ rewrite H3 in H12. inversion H12. 
    ++ rewrite H3 in H12. inversion H12. 
    ++ rewrite H3 in H11. inversion H11. subst. apply H4 in H13. destruct H13.
    ++ rewrite H3 in H11. inversion H11. reflexivity.
    ++ rewrite H3 in H13. inversion H13. 
  + inversion H0; subst.
    ++ rewrite H5 in H9. inversion H9. 
    ++ rewrite H5 in H9. inversion H9. 
    ++ rewrite H5 in H9. inversion H9. 
    ++ rewrite H5 in H8. inversion H8. 
    ++ rewrite H5 in H8. inversion H8. 
    ++ reflexivity.
Qed.

(** Definição Funcional de Passo de Computação . *)

Definition next_step (prog : program) (snap : snapshot) : snapshot :=
  match snap with
  | SNAP n s =>
    match nth_error prog n with
    | Some ([l] x <- + 1) => SNAP (n + 1) (incr s x)
    | Some ([l] x <- - 1) => SNAP (n + 1) (decr s x)
    | Some ([l] x <- + 0) => SNAP (n + 1) s
    | Some ([l] IF x GOTO j) =>
        match s x with
        | S m => SNAP (get_labeled_instr prog j) s
        | 0   => SNAP (n + 1) s
        end
    | None => SNAP n s
    end
  end.

(** Prova de Equivalência da Versão Funcional e da Propriedade *)

Theorem next_step_equivalence:
  forall p snap1 snap2,
  (next_step p snap1) = snap2 <-> steps_to p snap1 snap2.
Proof.
  intros. split.
  - intros. destruct snap1. simpl in H. destruct (nth_error p n) eqn:E.
    + destruct i. destruct s0; subst; try (econstructor); (try reflexivity);
      try(eassumption).
     ++ destruct (s v) eqn:E2.
        +++ eapply S_If_0; try (eassumption); reflexivity.
        +++ eapply S_If_S; try (eassumption); try (reflexivity).
            * intros H. rewrite E2 in H. discriminate H.
    + subst. apply S_Out. assumption.
  - intros H. unfold next_step. inversion H; subst; rewrite H0;
    try(reflexivity).
     ++ rewrite H1; reflexivity.
     ++ destruct (st x).
        +++ exfalso. apply H1. reflexivity.
        +++ reflexivity.
Qed.

(** Computação : Não é o mesmo conceito de computação do livro, já que não
    precisamos finalizar na snapshot terminal.
    Aqui é basicamente uma aplicação sucessiva de next_steps. *)

Fixpoint compute_program (p : program) snap n :=
  match n with
  | S n' => compute_program p ((next_step p snap )) n'
  | O    => snap
  end.

Definition HALT (s : state) (p : program) (n : nat) :=
  let inital_snap := SNAP 0 s in 
  let nth_snap := compute_program p inital_snap n in 

  match nth_snap with 
  | SNAP n' _ => n' = (length p) 
  end.

(** Função Definida pelo Programa:

    L é a lista de variáveis iniciais. A ideia é interpretar o programa como
   uma função de n variáveis

   phi_p (x1, x2, x3, x4). *)


Definition get_Y (p : program) (x : nat) (n : nat) :=
  match (compute_program p (SNAP 0 (create_state x)) n) with
  | SNAP _ s => s Y
  end.

Definition partially_computable (f : nat -> option nat) := 
  exists (p : program), forall x,
    (f x = None -> forall (s : state) (k : nat), ~ (HALT s p k)) /\ 
    (f x <> None -> exists (k : nat), HALT (create_state x) p k /\ 
    Some (get_Y  p x k) = (f x)).


(* ################################################################# *)
