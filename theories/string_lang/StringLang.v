(** * StringLang: Linguagem Simples Baseada em Strings *)

From Stdlib Require Import Nat.
From Stdlib Require Import List.
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
              | Instr _ (APPEND k _) => k <= n /\ program_over t n
              | Instr _ (IF_ENDS_GOTO _ k _) => k <= n /\ program_over t n
              | _ => program_over t n
              end
  end.

Definition state := variable -> string.


Fixpoint string_over s n :=
  match s with
  | [] => True
  | h :: t => h <= n /\ string_over t n
  end.

Definition state_over (st : state) n :=
  forall x, string_over (st x) n.

  

Definition empty : state  := fun _ => [].

(** Auxiliares **)

Definition eq_inst_label  (instr : instruction ) (opt_lbl : option label) :=
  match instr, opt_lbl with 
  | Instr (Some lbl_a) _, Some lbl_b => eqb_lbl lbl_a lbl_b
  | _, _                => false
  end.

Fixpoint get_labeled_instr (p : program)
                                (lbl : option label)
                                : option nat :=
  match p with
  | [] => None
  | h :: t =>
      match get_labeled_instr t lbl with
      | Some n => Some (S n)
      | None =>
          if eq_inst_label h lbl
          then Some 0
          else None
      end
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
  | SNAP : option nat -> state -> snapshot.


Lemma state_over_iter (st : state) (n : nat) :
  state_over st n ->
  forall str var,
  string_over str n ->
  state_over (update st var str) n.
Proof.
  intros. unfold state_over in *. 
  intros x. unfold update. destruct (eqb_var var x); auto.
Qed.

Lemma string_over_tl : forall st n,
  state_over st n ->
  forall x,
  string_over (tl (st x)) n.
Proof.
  intros. unfold state_over in *.
  destruct (st x) eqn:E.
  + simpl. auto.
  + simpl. pose proof (H x). rewrite E in H0.
    simpl in H0. apply H0.
Qed.

Lemma string_over_app : forall h t n,
  string_over h n ->
  string_over t n ->
  string_over (h ++ t) n.
Proof.
  intros. induction h; auto.
  + simpl in *. destruct H; split; auto.
Qed.

Ltac solve_string :=
  repeat (
    match goal with
    | |- _ => apply StringLang.state_over_iter
    | |- _ => apply string_over_tl
    | |- _ => apply string_over_app
    | |- _ => apply state_over_iter
    end; simpl; auto
  ).




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


Notation "'[ i1 ; .. ; iN ]'" := (cons iN .. (cons i1 nil) ..)
  (at level 0, i1 custom com', iN custom com') : string_lang_scope.

Open Scope string_lang_scope.



Definition ends_with (s : string) (n : nat) :=
  match s with 
  | [] => false
  | h :: t => h =? n
  end.

Definition decr_option n :=
  match n with 
  | 0 => None
  | S n => Some n 
  end.

Definition next_step (prog : program) (snap : snapshot) : snapshot :=
  match snap with
  | SNAP opt_line s => 
         match opt_line with
         | None   => SNAP None s
         | Some n => let decr_line := decr_option n in
            match nth_error prog n with
            | Some <{[_] x <- + v }> => SNAP decr_line (append v s x)
            | Some <{[_] x <- -   }> => SNAP decr_line (del s x)
            | Some <{[_] IF x ENDS v GOTO l}> =>
                match (ends_with (s x) v ) with 
                | true  => SNAP (get_labeled_instr prog l) s
                | false => SNAP decr_line s
                end
            | None => SNAP None s (* Caso impossível com snap começando certo *)
            end
         end
 end.


Fixpoint compute_program (p : program ) snap n :=
  match n with
  | S n' => next_step p (compute_program p snap n')
  | O    => snap
  end.


Definition split_snap (snap : snapshot) :=
  match snap with
  | SNAP i s => (i, s)
  end.


(* 
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

 *) 

(* ################################################################ *)
