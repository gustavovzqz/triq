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
  | IF_GOTO   : variable -> option label -> statement
  | SKIP : variable -> statement.

Inductive instruction : Type :=
  | Instr : option label -> statement -> instruction.

Definition program := list instruction.

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
         (IF_GOTO x y) 
           (in custom com at level 89, x at level 99,
            y at level 99) : com_scope.

Notation "[ l ] s " := (Instr (l) s)
  (at level 0, s custom com at level 200) : com_scope.

Notation "[ ] s " := (Instr None s)
  (at level 0, s custom com at level 200) : com_scope.


Notation "'[ i1 ; .. ; iN ]'" := (cons i1 .. (cons iN nil) ..)
  (at level 0, i1 custom com, iN custom com) : com_scope.

Open Scope com_scope.

Definition eq_inst_label (instr : instruction ) (opt_lbl : option label) :=
  match instr, opt_lbl with 
  | Instr (Some lbl_a) _, Some lbl_b => eqb_lbl lbl_a lbl_b
  | _, _                => false
  end.

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


(** Exemplos *)



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

Inductive snapshot :=
  | SNAP : nat -> state -> snapshot.

Inductive step : program -> snapshot -> snapshot -> Prop :=
  | S_Incr : forall program x i opt_lbl instruction st,
      nth_error program i = Some instruction ->
      instruction = ([opt_lbl] x <- + 1)     ->
      step program (SNAP i st) (SNAP (i + 1) (t_incr st x))

  | S_Decr: forall program x i opt_lbl instruction st,
      nth_error program i = Some instruction ->
      (instruction = ([opt_lbl] x <- - 1))   ->
      step program (SNAP i st) (SNAP (i + 1) (t_decr st x))

  | S_Skip: forall program x i opt_lbl instruction st,
      nth_error program i = Some instruction ->
      instruction = ([opt_lbl] x <- + 0 )    ->
      step program (SNAP i st) (SNAP (i + 1) (t_decr st x))

  | S_If_S: forall program x i opt_lbl l instruction st,
      nth_error program i = Some instruction   ->
      st x = 0                                 ->
      (instruction = ([opt_lbl] IF x GOTO l )) ->
      step program (SNAP i st) (SNAP (i + 1) (t_decr st x))

  | S_If_0: forall program x i j opt_lbl l instruction st,
      nth_error program i = Some instruction ->
      st x <> 0                              ->
      instruction = ([opt_lbl] IF x GOTO l ) ->
      (get_labeled_instr program opt_lbl = j)                -> 
      step program (SNAP i st) (SNAP j (t_decr st x)).




Definition x := X 0.
Definition x1 := X 1.
Definition l := Some (A 0).
Definition y := Y.

Check (Instr None (INCR (X 0))).

Check ([l] x <- + 1).

Definition prg : program :=
  <{[ [l] x  <- + 1;
      [ ] x  <- - 1;
      [ ] x  <- + 0;
      [ ] IF x GOTO l ]}>.

Definition state_t1 := t_incr initial_state x.


Theorem exemplo : step prg (SNAP 0 initial_state) (SNAP 1 state_t1).
Proof.
  unfold prg. destruct l; eapply S_Incr; reflexivity.
Qed.


End SLang.
