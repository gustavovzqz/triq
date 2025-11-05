(** * StringLang: Linguagem Simples Baseada em Strings *)

From Coq Require Import Nat.
From Coq Require Import List.
From Triq Require Export LanguagesCommon.

Import ListNotations.


(** O que é uma String?

  - No modulo String, ela é definida como uma lista de caracteres ASCII, que,
   por sua vez, é basicamente um booleano de oito dígitos.

   Inductive ascii : Set := Ascii (_ _ _ _ _ _ _ _ : bool).

   Inductive string : Set :=
     | EmptyString : string
     | String : ascii -> string -> string. *)

(** A definição de strings acima não é suficiente para suprir as necessidades
    da nossa linguagem. 

   "We could also define a regex matcher over polymorphic lists,
    not lists of ASCII characters specifically. The matching algorithm
    that we will implement needs to be able to test equality of elements in 
    a given list, and thus needs to be given an equality-testing function.
    Generalizing the definitions, theorems, and proofs that we define
    for such a setting is a bit tedious, but workable."
    - https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html#lab287 *)


(** Alfabetos:

  1. Conjuntos finitos;
  2. Precisamos indexar para formar o programa de alfabeto 0, 1, ..., n;
  3. É útil atribuir uma ordem aos elementos do conjunto! *)




(* Conjunto com com os dígitos [0, ..., n] *)

Definition alphabet n := {k : nat | k <= n}.


Definition eqb_char {n : nat} (a : alphabet n) (b : alphabet n) :=
  proj1_sig a =? proj1_sig b.

(* 
   Alfabeto 1   ->  {}, 0, 00, 000, ...
   Alfabeto 2   ->  {}, 0, 1, 00, 01, 10, 11
   Alfabeto 9   ->  {}, 0, 1, 2, 3, 4, 5, 6, 7, 8, 00, 01

   Não é exatamente como nós compomos as nossas bases já que não há dígito
   com valor zero (usamos a string vazia). Começar com 1 em vez de zero também
   não adianta muito:

   Alfabeto 9   ->  {}, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, ...,

   Não tem o 10! *)


Definition string (n : nat) := list (alphabet n).

(** Elementos de um Programa: *)


Inductive statement (n : nat) : Type :=
  | APPEND: (alphabet n) -> variable -> statement n
  | DEL : variable -> statement n
  | IF_ENDS_GOTO   : variable -> (alphabet n) -> option label -> statement n.

Inductive instruction (n : nat) : Type :=
  | Instr : option label -> statement n -> instruction n.

Definition program (n : nat)  := list (instruction n).

Definition state (n : nat) := variable -> (string n).

Definition empty (n : nat) : (state n) := fun _ => [].

Arguments Instr{n}.


(** Auxiliares **)

Definition eq_inst_label {n : nat} (instr : instruction n ) (opt_lbl : option label) :=
  match instr, opt_lbl with 
  | Instr (Some lbl_a) _, Some lbl_b => eqb_lbl lbl_a lbl_b
  | _, _                => false
  end.


Definition get_labeled_instr {n : nat} (p : program n) (lbl : option label) :=
  let fix aux l n :=
    match l with 
    | h :: t => match (eq_inst_label h lbl) with 
                | true => n
                | false => aux t (n + 1)
                end
    | []     => n 
    end
  in aux p 0.



Definition update {n : nat} (m : state n) (x : variable) (v : string n) :=
  fun x' => if eqb_var x x' then v else m x'.

Definition append {n : nat} (h : (alphabet n)) (m : state n ) (x : variable) :=
  let v := m x in 
  update m x (h :: v).


Definition create_state (n : nat) x :=
  update (empty n) (X 0) x.

Search list.

Print removelast.

Definition del {n : nat} (m : state n) (x : variable) :=
  let v := m x in 
  update m x (removelast v).

Inductive snapshot n :=
  | SNAP : nat -> (state n) -> snapshot n.

Arguments SNAP{n}.
Arguments APPEND{n}.
Arguments DEL{n}.
Arguments IF_ENDS_GOTO{n}.


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



Fixpoint ends_with {n : nat} (l : string n) (h : alphabet n) :=
  match l with
  | [] => false 
  | [a] => eqb_char a h
  | a :: (_ :: _) as l' => ends_with l' h
  end.



(** Propriedade de Passo de Computação: *)

 Inductive steps_to {n : nat} : (program n) ->
  (snapshot n) -> (snapshot n) -> Prop :=

  (* V <- s V *)
  | S_Append : forall (h : alphabet n) 
      (p : program n) (i : nat) (instr : instruction n) (st : state n)
      (x : variable) opt_lbl,
      nth_error p i = Some instr -> 
      instr = <{[opt_lbl] x <- + h}> ->
      steps_to p (SNAP i st) (SNAP (i + 1) (append h st x))

  (* V <- v- *)
  | S_Del: forall
      (p : program n) (i : nat) (instr : instruction n) (st : state n)
      (x : variable) opt_lbl,
      nth_error p i = Some instr -> 
      instr = <{[opt_lbl] x <- - }> ->
      steps_to p (SNAP i st) (SNAP (i + 1) (del st x))

  (* IF V ends s GOTO l -> if = true *)
  | S_If_True: forall (h : alphabet n)
      (p : program n) (i : nat) (instr : instruction n) (st : state n)
      (x : variable) opt_lbl l j,
      nth_error p i = Some instr ->
      instr = <{[opt_lbl] IF x ENDS h GOTO l}> ->
      ends_with (st x) h = true ->
      get_labeled_instr p l = j ->
      steps_to p (SNAP i st) (SNAP j st)

  (* IF V ends s GOTO l -> if = false *)
  | S_If_False: forall (h : alphabet n)
      (p : program n) (i : nat) (instr : instruction n) (st : state n)
      (x : variable) opt_lbl l,
      nth_error p i = Some instr ->
      instr = <{[opt_lbl] IF x ENDS h GOTO l}> ->
      ends_with (st x) h = false ->
      steps_to p (SNAP i st) (SNAP (i + 1) st)

  (* Fora dos limites do programa *)
  | S_Out : forall (p : program n) (i : nat) (st : state n),
      nth_error p i = None ->
      steps_to p (SNAP i st) (SNAP i st).





(* f é parcialmente computável em NatLang ->
   f é parcialmente computável em StringLang n para todo n ->
   f é computável estritamente por um programa Post-Turing ->
   f é computável por um programa Post-Turing ->
   f é parcialmente computável em NatLang. *)


Definition next_step {n : nat} (p : program n) (snap : snapshot n) :=
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
  forall n (p : program n) snap1 snap2,
  (next_step p snap1) = snap2 <-> steps_to p snap1 snap2.
Proof.
  intros. split.
  (* -> *)
  - intros. destruct snap1. simpl in H. destruct (nth_error p n0) eqn:E.
    + destruct i. destruct s0; subst; try(econstructor); try(eassumption);
      try(reflexivity).
      ++ destruct (ends_with (s v) a) eqn:E1.
         +++ eapply S_If_True; try(reflexivity); try(eassumption).
         +++ eapply S_If_False; try(reflexivity); try(eassumption).
    + subst. apply S_Out. assumption.
  (* <- *)
  - intros. unfold next_step. inversion H; subst; rewrite H0; try(reflexivity).
    + rewrite H2. reflexivity.
    + rewrite H2. reflexivity.
Qed.



Fixpoint compute_program {m : nat} (p : program m ) snap n :=
  match n with
  | S n' => next_step p (compute_program p snap n')
  | O    => snap
  end.


Definition get_state {k : nat} (p : program k ) n :=
  let initial_snapshot := SNAP 0 (empty k) in 
  match (compute_program p initial_snapshot n) with 
  | SNAP _ s => s
  end.

Definition HALT {m : nat} (s : state m ) (p : program m) (n : nat) :=
  let initial_snap := SNAP 0 s in 
  let nth_snap := compute_program p initial_snap n in 

  match nth_snap with 
  | SNAP n' _ => n' = (length p) 
  end.


Definition get_Y {n : nat} (p : program n ) (x : string n) (k : nat) :=
  match (compute_program p (SNAP 0 (create_state n x)) n) with
  | SNAP _ s => s Y
  end.


Definition partially_computable (n : nat) 
  (f : (string n) -> option (string n)) := 
  exists (p : program n), forall x,
    (f x = None -> forall (k : nat), ~ (HALT (create_state n x) p k)) /\ 
    (f x <> None -> exists (k : nat), HALT (create_state n x) p k /\ 
    Some (get_Y  p x k) = (f x)).


Definition partially_computable_by_p (n : nat) 
  (f : (string n) -> option (string n)) (p : program n) := 
    forall x,
    (f x = None -> forall (k : nat), ~ (HALT (create_state n x) p k)) /\ 
    (f x <> None -> exists (k : nat), HALT (create_state n x) p k /\ 
    Some (get_Y  p x k) = (f x)).


(* ################################################################# *)
