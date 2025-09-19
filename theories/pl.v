From Stdlib Require Import Nat.
From Stdlib Require Import List.
Import ListNotations.

Module SLang.

(** Variáveis e Labels *)

Inductive variable : Type :=
  | X : nat -> variable  (* input  *)
  | Z : nat -> variable  (* local  *)
  | Y : variable.        (* output *)
Inductive label : Type :=
  | A : nat -> label.

Inductive statement : Type :=
  | INCR : variable -> statement
  | DECR : variable -> statement
  | IF   : variable -> label -> statement
  | SKIP : variable -> statement.

Inductive instruction : Type :=
  | L_instr : label -> statement -> instruction
  | instr   : statement -> instruction.

Definition program := list instruction.

Definition eqb_var v1 v2 := 
  match v1, v2 with 
  | X a, X b => a =? b
  | Z a, Z b => a =? b
  | Y, Y  => true
  | _, _ => false
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

(** Notações adaptadas de: https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html *)
(* TODO: Aprender... *)

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

Notation "x <- + 0" := (SKIP x)
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

Check (instr (INCR (X 0))).

(* Check ([ ] (X 0) <- + 1). *)


Definition prg : program :=
  <{[ [l] x  <- + 1;
      [ ] x  <- - 1;
      [ ] x  <- + 0;
      [ ] IF x GOTO l ]}>.

(** Estado de um Programa *)
(* Referências: 
  https://softwarefoundations.cis.upenn.edu/lf-current/Maps.html
  https://github.com/gustavovzqz/coq-lambda/blob/main/theories/Lambda.v
*)

Definition state := variable -> nat.

Definition initial_state : state := (fun _ => 0).

Definition t_update (m : state ) (x : variable) (v : nat) :=
  fun x' => if eqb_var x x' then v else m x'.

Definition t_incr (m : state ) (x : variable) :=
  let v := m x in 
  fun x' => if eqb_var x x' then (v + 1) else m x'.

Definition t_decr (m : state ) (x : variable) :=
  let v := m x in 
  fun x' => if eqb_var x x' then (v - 1) else m x'.

Inductive step : program -> (nat * state) -> (nat * state) -> Prop :=
  | S_Incr : forall p x i m l ins,
      nth_error p i = Some ins ->
      (ins = instr (INCR x) \/ ins = L_instr l (INCR x)) ->
      step p (i, m) (i + 1, t_incr m x)

  | S_Decr : forall p x i m l ins,
      nth_error p i = Some ins ->
      (ins = instr (DECR x) \/ ins = L_instr l (DECR x)) ->
      step p (i, m) (i + 1, t_decr m x)

  | S_Skip : forall p x i m l ins,
      nth_error p i = Some ins ->
      (ins = instr (SKIP x) \/ ins = L_instr l (SKIP x)) ->
      step p (i, m) (i + 1, m).

(* Completar... *)

End SLang.
