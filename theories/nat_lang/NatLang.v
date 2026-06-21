(** * NatLang: Linguagem Simples Baseada em Naturais *)

(** O objetivo desse arquivo é definir uma linguagem extremamente simples
    que lida com naturais. A linguagem é baseada na linguagem simples de 
    três instruções apresentada no livro _Computability, Complexity and Languages_.

    Apesar de simples, a linguagem possui diversas propriedades interessantes e já
    se trata de uma linguagem _Turing Completa_.

    Para prosseguir com a definição da linguagem, usaremos o arquivo [LanguagesCommon]
    que possui algumas definições úteis como [variable] e [label], comuns a outras 
    linguagens *)

From Stdlib Require Import Nat.
From Stdlib Require Import List.
Import ListNotations.

From Triq Require Export LanguagesCommon.

(** * Elementos Básicos de um Programa *)

(** A linguagem básica nos naturais possui apenas três instruções:

     - Incrementar o valor de uma variável em um (x <- x + 1);
     - Decrementar o valor de uma variável em um (x <- x - 1);
     - Pulo direcional para uma instrução com certa label, dependendo
         do valor da variável. (IF X != 0 GOTO A).

   Cada instrução pode ou não possuir uma label. Confira o exemplo abaixo:

     - [A0] X0 <- X0 + 1
     - [  ] X1 <- X1 - 1 (* Não possui label *)
     - [B1] IF X0 != 0 GOTO A

   Conversaremos mais sobre os detalhes de cada instrução quando definirmos
   o significado de computação. *)

(** ** Statement e Instruction *)

(** Como cada instrução pode ou não possuir uma label, nós separamos o conceito
    de [statement] e de [instruction]. Um [statement] é simplesmente o _corpo_
    da instrução, e a instrução de fato é a junção com a informação da label.

    Veja que o IF GOTO também recebe uma [option label] como argumento. O razão
    disso é para que exista a possibilidade de have um GOTO para nenhuma
    instrução. Veremos posteriormente que isso fará com que o programa
    termine. *)

Inductive statement : Type :=
  | INCR : variable -> statement
  | DECR : variable -> statement
  | IF_GOTO   : variable -> option label -> statement.


Inductive instruction : Type :=
  | Instr : option label -> statement -> instruction.

Definition program := list instruction.

(** ** Notações *)

(** As notações abaixo simplificarão um pouco nossos trabalhos na escrita de
    programas para teste. As notações foram extraídas com pequenas adaptações
    de um exemplo em: 
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



Notation "'IF' x 'GOTO' y " :=
         (IF_GOTO x y) 
           (in custom com at level 89, x at level 99,
            y at level 99) : nat_lang_scope.

Notation "[ l ] s " := (Instr (l) s)
  (at level 0, s custom com at level 200) : nat_lang_scope.

Notation "[ ] s " := (Instr None s)
  (at level 0, s custom com at level 200) : nat_lang_scope.


Notation "'[ i1 ; .. ; iN ]'" := (cons iN .. (cons i1 nil) ..)
  (at level 0, i1 custom com, iN custom com) : nat_lang_scope.

Open Scope nat_lang_scope.


(** ** Estado de um Programa *)

(** Para representar o estado do programa, precisamos de um _mapa_ que
    associa cada variável a um valor nos naturais. Como representação
    simples, podemos simplesmente *)

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
  | SNAP : option nat -> state -> snapshot.

(* Veja que uma snapshot inicial de um programa possivelmente possuirá
  valores de x1, x2, x3... inicialmente atribuídos *)

Definition initial_snapshot := SNAP (Some 0) empty.

Definition create_state x :=
  update empty (X 0) x.


(** Decidibilidade e Auxiliares Envolvendo Igualdades *)


Definition eq_inst_label (instr : instruction ) (opt_lbl : option label) :=
  match instr, opt_lbl with 
  | Instr (Some lbl_a) _, Some lbl_b => eqb_lbl lbl_a lbl_b
  | _, _                => false
  end.

(** Função para encontrar a posição da primeira instrução com certa label 
    em um programa *)

(** MUDOU COM INV *)

Fixpoint get_labeled_instr (p : list instruction)
                                (lbl : option label)
                                : option nat :=
  match p with
  | [] => None
  | h :: t =>
      match get_labeled_instr t lbl with
      | Some n => Some (S n)      (* já existe uma ocorrência mais à frente *)
      | None =>
          if eq_inst_label h lbl
          then Some 0             (* ocorrência atual *)
          else None
      end
  end.



(** Definição Funcional de Passo de Computação . *)


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
            | Some ([l] x <- + 1) => SNAP decr_line (incr s x)
            | Some ([l] x <- - 1) => SNAP decr_line (decr s x)
            | Some ([l] IF x GOTO j) =>
                match s x with
                | S m => SNAP (get_labeled_instr prog j) s
                | 0   => SNAP decr_line s
                end
            | None => SNAP None s (* Caso impossível com snap começando certo *)
            end
         end
 end.


Fixpoint compute_program (p : program) snap n :=
  match n with
  | S n' => next_step p (compute_program p snap n')
  | O    => snap
  end.

Definition split_snap (snap : snapshot) :=
  match snap with
  | SNAP i s => (i, s)
  end.


(* TODO: Vou fazer com o estado inicial por enquanto, mas provavelmente vai ser
   necessário trocar para receber um valor de X como entrada *)

Definition get_state (p : program) n :=
  match (compute_program p initial_snapshot n) with 
  | SNAP _ s => s
  end.


(* Não é usado, mas vai ser em algum momento *) 
(* 
Definition HALT (s : state) (p : program) (n : nat) :=
  let inital_snap := SNAP 0 s in 
  let nth_snap := compute_program p inital_snap n in 

  match nth_snap with 
  | SNAP n' _ => n' = (length p) 
  end.


(** Função Parcialmente Computável por NatLang *)

Definition get_Y (p : program) (x : nat) (n : nat) :=
  match (compute_program p (SNAP 0 (create_state x)) n) with
  | SNAP _ s => s Y
  end.

Definition partially_computable (f : nat -> option nat) := 
  exists (p : program), forall x,
    (f x = None -> forall (k : nat), ~ (HALT (create_state x) p k)) /\ 
    (f x <> None -> exists (k : nat), HALT (create_state x) p k /\ 
    Some (get_Y  p x k) = (f x)).


Definition partially_computable_by_p (f : nat -> option nat) p := 
    forall x,
    (f x = None -> forall (k : nat), ~ (HALT (create_state x) p k)) /\ 
    (f x <> None -> exists (k : nat), HALT (create_state x) p k /\ 
    Some (get_Y  p x k) = (f x)).
*)


(* ################################################################# *)


