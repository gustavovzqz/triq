(** * StringLang: Linguagem Simples Baseada em Strings *)

From Coq Require Import Nat.
From Coq Require Import List.
From Triq Require Export LanguagesCommon.

Import ListNotations.


Definition string := list nat.

(** Elementos de um Programa: *)


Inductive statement : Type :=
  | APPEND: nat -> variable -> statement
  | DEL : variable -> statement
  | IF_ENDS_GOTO   : variable -> nat -> option label -> statement.

Inductive instruction : Type :=
  | Instr : option label -> statement  -> instruction.

Definition program := list (instruction).

Fixpoint program_over prog n :=
  match prog with 
  | [] => True
  | h :: t => match h with 
              | Instr _ (APPEND k _) => le k n /\ program_over t n
              | Instr _ (IF_ENDS_GOTO _ k _) => le k n /\ program_over t n
              | _ => False
              end
  end.


Definition state := variable -> string.

Definition empty : state  := fun _ => [].

(** Auxiliares **)

Definition eq_inst_label  (instr : instruction ) (opt_lbl : option label) :=
  match instr, opt_lbl with 
  | Instr (Some lbl_a) _, Some lbl_b => eqb_lbl lbl_a lbl_b
  | _, _                => false
  end.

Fixpoint get_labeled_instr (p : program) (lbl : option label) : nat :=
  match p with
  | [] => 0
  | h :: t =>
      if eq_inst_label h lbl
      then 0
      else 1 + get_labeled_instr t lbl
  end.

Definition update (m : state ) (x : variable) (v : string ) :=
  fun x' => if eqb_var x x' then v else m x'.

Definition append (h : nat) (m : state) (x : variable) :=
  let v := m x in 
  update m x (v ++ [h]).

Definition create_state  x :=
  update empty (X 0) x.

Definition del (m : state) (x : variable) :=
  let v := m x in 
  update m x (tl v).

Inductive snapshot :=
  | SNAP : nat -> state -> snapshot.

Declare Custom Entry com'.
Declare Scope string_lang_scope.
Declare Custom Entry com_aux'.

Notation "<{ e }>" := e (e custom com_aux') : string_lang_scope.
Notation "e" := e (in custom com_aux' at level 0, e custom com') : string_lang_scope.
Notation "( x )" := x (in custom com', x at level 99) : string_lang_scope.
Notation "x" := x (in custom com' at level 0, x constr at level 0) : string_lang_scope.

Notation "x <- + v" := (APPEND v x)
  (in custom com' at level 50, left associativity).

Notation "x <- -" := (DEL x)
  (in custom com' at level 50, left associativity).



Notation "'IF' x 'ENDS' k 'GOTO' y " :=
         (IF_ENDS_GOTO x k y) 
           (in custom com' at level 89, x at level 99,
            y at level 99) : string_lang_scope.

Notation "[ l ] s " := (Instr (l) s)
  (at level 0, s custom com' at level 200) : string_lang_scope.

Notation "[ ] s " := (Instr None s)
  (at level 0, s custom com' at level 200) : string_lang_scope.


Notation "'[ i1 ; .. ; iN ]'" := (cons i1 .. (cons iN nil) ..)
  (at level 0, i1 custom com', iN custom com') : string_lang_scope.

Open Scope string_lang_scope.



Definition ends_with (s : string) (n : nat) :=
  match s with 
  | [] => false
  | h :: t => h =? n
  end.


(** Propriedade de Passo de Computação: *)

 Inductive steps_to : program -> snapshot -> snapshot -> Prop :=

  (* V <- s V *)
  | S_Append : forall (h : nat) 
      (p : program) (i : nat) (instr : instruction) (st : state)
      (x : variable) opt_lbl,
      nth_error p i = Some instr -> 
      instr = <{[opt_lbl] x <- + h}> ->
      steps_to p (SNAP i st) (SNAP (i + 1) (append h st x))

  (* V <- v- *)
  | S_Del: forall
      (p : program) (i : nat) (instr : instruction) (st : state)
      (x : variable) opt_lbl,
      nth_error p i = Some instr -> 
      instr = <{[opt_lbl] x <- - }> ->
      steps_to p (SNAP i st) (SNAP (i + 1) (del st x))

  (* IF V ends s GOTO l -> if = true *)
  | S_If_True: forall (h : nat)
      (p : program) (i : nat) (instr : instruction) (st : state)
      (x : variable) opt_lbl l j,
      nth_error p i = Some instr ->
      instr = <{[opt_lbl] IF x ENDS h GOTO l}> ->
      ends_with (st x) h = true ->
      get_labeled_instr p l = j ->
      steps_to p (SNAP i st) (SNAP j st)

  (* IF V ends s GOTO l -> if = false *)
  | S_If_False: forall (h : nat)
      (p : program) (i : nat) (instr : instruction) (st : state)
      (x : variable) opt_lbl l,
      nth_error p i = Some instr ->
      instr = <{[opt_lbl] IF x ENDS h GOTO l}> ->
      ends_with (st x) h = false ->
      steps_to p (SNAP i st) (SNAP (i + 1) st)

  (* Fora dos limites do programa *)
  | S_Out : forall (p : program) (i : nat) (st : state),
      nth_error p i = None ->
      steps_to p (SNAP i st) (SNAP i st).





(* f é parcialmente computável em NatLang ->
   f é parcialmente computável em StringLang n para todo n ->
   f é computável estritamente por um programa Post-Turing ->
   f é computável por um programa Post-Turing ->
   f é parcialmente computável em NatLang. *)


Definition next_step (p : program) (snap : snapshot) :=
  match snap with 
  | SNAP n s =>
      match nth_error p n with 
      | Some <{[_] x <- + v }> => SNAP (n + 1) (append v s x)
      | Some <{[_] x <- -   }> => SNAP (n + 1) (del s x)
      | Some <{[_] IF x ENDS v GOTO l}> =>
          match (ends_with (s x) v ) with 
          | true  => SNAP (get_labeled_instr p l) s
          | false => SNAP (n + 1) s
          end
      | None => SNAP n s
      end
  end.


(** Prova de Equivalência da Versão Funcional e da Propriedade *)

Theorem next_step_equivalence :
  forall (p : program) snap1 snap2,
  (next_step p snap1) = snap2 <-> steps_to p snap1 snap2.
Proof.
  intros. split.
  (* -> *)
  - intros. destruct snap1. simpl in H. destruct (nth_error p n) eqn:E.
    + destruct i. destruct s0; subst; try(econstructor); try(eassumption);
      try(reflexivity).
      ++ destruct (ends_with (s v) n0) eqn:E1.
         +++ eapply S_If_True; try(reflexivity); try(eassumption).
         +++ eapply S_If_False; try(reflexivity); try(eassumption).
    + subst. apply S_Out. assumption.
  (* <- *)
  - intros. unfold next_step. inversion H; subst; rewrite H0; try(reflexivity).
    + rewrite H2. reflexivity.
    + rewrite H2. reflexivity.
Qed.



Fixpoint compute_program (p : program ) snap n :=
  match n with
  | S n' => next_step p (compute_program p snap n')
  | O    => snap
  end.


Definition get_state (p : program ) n :=
  let initial_snapshot := SNAP 0 (empty) in 
  match (compute_program p initial_snapshot n) with 
  | SNAP _ s => s
  end.

Definition HALT (s : state) (p : program) (n : nat) :=
  let initial_snap := SNAP 0 s in 
  let nth_snap := compute_program p initial_snap n in 

  match nth_snap with 
  | SNAP n' _ => n' = (length p) 
  end.


Definition get (y : variable)  (p : program) (x : string) (k : nat) :=
  match (compute_program p (SNAP 0 (create_state x)) k) with
  | SNAP _ s => s y
  end.


Definition partially_computable (n : nat) 
  (f : (string) -> option (string)) := 
  exists (p : program), forall x,
    (f x = None -> forall (k : nat), ~ (HALT (create_state x) p k)) /\ 
    (f x <> None -> exists (k : nat), HALT (create_state x) p k /\ 
    Some (get Y  p x k) = (f x)).


Definition partially_computable_by_p (n : nat) 
  (f : (string) -> option (string)) (p : program) := 
    forall x,
    (f x = None -> forall (k : nat), ~ (HALT (create_state x) p k)) /\ 
    (f x <> None -> exists (k : nat), HALT (create_state x) p k /\ 
    Some (get Y  p x k) = (f x)).


(* ################################################################ *)
