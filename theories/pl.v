From Coq Require Import Nat.
From Coq Require Import List.
Import ListNotations.

(** Variáveis e Labels *)

Inductive variable : Type :=
  | X : nat -> variable  (* input *)
  | Z : nat -> variable  (* local *)
  | Y : variable.

Inductive label : Type :=
  | A : nat -> label.

Inductive statement : Type :=
  | INCR : variable -> statement
  | DECR : variable -> statement
  | IF   : variable -> label -> statement.

Inductive instruction : Type :=
  | L_instr : label -> statement -> instruction
  | instr   : statement -> instruction.

Definition program := list instruction.

(** Notações adaptadas de: https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html *)

Declare Custom Entry com.
Declare Scope com_scope.
Declare Custom Entry com_aux.

Notation "<{ e }>" := e (e custom com_aux) : com_scope.
Notation "e" := e (in custom com_aux at level 0, e custom com) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.

Notation "x <- + 1" := (INCR x)
  (in custom com at level 50, left associativity).
Notation "x <- - 1" := (DECR x)
  (in custom com at level 50, left associativity).
Notation "'IF' x 'GOTO' y " :=
         (IF x y) 
           (in custom com at level 89, x at level 99,
            y at level 99) : com_scope.
Notation "[ l ] s " := (L_instr l s)
  (at level 0, s custom com at level 200) : com_scope.

Notation "[ ] s " := (instr  s)
  (at level 0, s custom com at level 200) : com_scope.


Notation "'[ i1 ; .. ; iN ]'" := (cons i1 .. (cons iN nil) ..)
  (at level 0, i1 custom com, iN custom com) : com_scope.

Open Scope com_scope.



(** Exemplos *)

Definition x := X 0.
Definition x1 := X 1.
Definition l := A 0.
Definition y := Y.

Check (<{x <- + 1}>).


Definition prg : program :=
  <{[ [l] x <-  + 1;
      [ ] x1 <- - 1;
      [ ] IF x GOTO l ]}>.

