(** * StringLang: Linguagem Simples Baseada em Strings *)

From Stdlib Require Import Nat.
From Stdlib Require Import List.

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



(* Definição possível um: *)

(* Conjunto com n dígitos *)

Definition alphabet n := {k : nat | k < n}.

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


(* Definição possível dois: 
   TODO: Apagar. *)

Inductive alphabet' (n : nat) : Type :=
  | CHAR : forall k : nat, 
            k < n -> alphabet' n.


Definition string (n : nat) := list (alphabet n).

(** Elementos de um Programa: *)

Inductive variable : Type :=
  | X : nat -> variable  (* input  *)
  | Z : nat -> variable  (* local  *)
  | Y : variable.        (* output *)

Inductive label : Type :=
  | A : nat -> label.

Inductive statement (n : nat) : Type :=
  | APPEND: (alphabet n) -> variable -> statement n
  | DEL : variable -> statement n
  | IF_ENDS_GOTO   : variable -> (alphabet n) -> option label -> statement n
  | SKIP : variable -> statement n.

Inductive instruction (n : nat) : Type :=
  | Instr : option label -> statement n -> instruction n.

Definition program (n : nat)  := list (instruction n).

Definition state (n : nat) := variable -> (string n).

Definition empty n : (state n) := fun _ => [].

Arguments APPEND{n}.
Arguments Instr{n}.

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

Search list.

Print removelast.

Definition del {n : nat} (m : state n) (x : variable) :=
  let v := m x in 
  update m x (removelast v).

Inductive snapshot n :=
  | SNAP : nat -> (state n) -> snapshot n.

Arguments SNAP{n}.
Arguments DEL{n}.
Arguments SKIP{n}.
Arguments IF_ENDS_GOTO{n}.


Search list.

Print last.


Fixpoint ends_with {n : nat} (l : string n) (h : alphabet n) :=
  match l with
  | [] => false 
  | [a] => eqb_char a h
  | a :: (_ :: _) as l' => ends_with l' h
  end.



(** Propriedade de Passo de Pomputação:

    steps_to programa s s' :=
    O programa de snapshot s possui como próxima snapshot s' *)

Inductive steps_to {n : nat} : (program n) ->
  (snapshot n) -> (snapshot n) -> Prop :=

  (* V <- s V *)
  | S_Append : forall (h : alphabet n) 
      (p : program n) (i : nat) (instr : instruction n) (st : state n)
      (x : variable) opt_lbl,
      nth_error p i = Some instr -> 
      instr = Instr opt_lbl (APPEND h x) ->
      steps_to p (SNAP i st) (SNAP (i + 1) (append h st x))

  (* V <- v- *)
  | S_Del: forall
      (p : program n) (i : nat) (instr : instruction n) (st : state n)
      (x : variable) opt_lbl,
      nth_error p i = Some instr -> 
      instr = Instr opt_lbl (DEL x) ->
      steps_to p (SNAP i st) (SNAP (i + 1) (del st x))

  (* v <- v *)
  | S_Skip: forall 
      (p : program n) (i : nat) (instr : instruction n) (st : state n)
      (x : variable) opt_lbl,
      nth_error p i = Some instr ->
      instr = Instr opt_lbl (SKIP x ) ->
      steps_to p (SNAP i st) (SNAP (i + 1) st)

  (* IF V ends s GOTO l -> if = true *)
  | S_If_True: forall (h : alphabet n)
      (p : program n) (i : nat) (instr : instruction n) (st : state n)
      (x : variable) opt_lbl l j,
      nth_error p i = Some instr ->
      instr = Instr opt_lbl (IF_ENDS_GOTO x h l) ->
      ends_with (st x) h = true ->
      get_labeled_instr p l = j ->
      steps_to p (SNAP i st) (SNAP j st)

  (* IF V ends s GOTO l -> if = false *)
  | S_If_False: forall (h : alphabet n)
      (p : program n) (i : nat) (instr : instruction n) (st : state n)
      (x : variable) opt_lbl l,
      nth_error p i = Some instr ->
      instr = Instr opt_lbl (IF_ENDS_GOTO x h l) ->
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








(** Exemplos! TODO: Mover para StringLangExamples depois da apresentação! *)


Theorem t0_lt_1 : 0 < 1.
Proof.
  constructor.
Qed.


Definition prg :=
  [ Instr None (APPEND (exist _ 0 t0_lt_1) (X 0))].

Check (prg : program 1).
