From Triq Require NatLang.
From Triq Require StringLang.
From Triq Require Import LanguagesCommon.

From Coq Require Import Nat.
From Coq Require Import List.
From Coq Require Extraction.
From Coq Require Import Lia.
Import ListNotations.

Search nat.

(** Conversão de String para Nat *)


(* n = 2
  [0, 1, 2] -> 3 elementos
   [1, 0, 0, 2, 1]
   2 * 3^4 + 1 * 3 *)

Definition string_to_nat {n : nat} (s : StringLang.string n) :=
  let fix aux l k {struct l}:=
  match l with 
  | h :: t => ((proj1_sig h + 1) * ((n + 1) ^ k)) + aux t (k - 1)
  | []  => 0
  end
   in aux s (length s - 1).


(** Conversão de Nat para String *)


(* Função de Incremento *)

Definition incr_string {n : nat} (s : StringLang.string n) : (StringLang.string n). Proof.
  refine (
  let fix aux l :=
  match l with 
  | h :: t => ((match (proj1_sig h <? (n) ) as eq return 
               ((proj1_sig h <? (n) = eq)) -> _ with
              | true  => fun _ => ((exist _ ((proj1_sig h) + 1) _) :: t)
              | false => fun _ => (exist _ 0 _) :: (aux t)
              end) _)
  | [] =>  [exist _ 0 _]
  end 
  in rev (aux (rev s))).
  ++ apply PeanoNat.Nat.le_0_l. 
  ++ rewrite PeanoNat.Nat.ltb_lt in e. unfold lt in e. 
     rewrite PeanoNat.Nat.add_comm. simpl. exact e.
  ++ apply PeanoNat.Nat.le_0_l.
  ++ reflexivity.
Defined.

Extraction incr_string.


(* Nat para String, basta usar o incremento n vezes *)

Fixpoint nat_to_string (k : nat) (n : nat) : (StringLang.string k)  :=
    match n with
    | S n' => incr_string (nat_to_string k n')
    | 0 => []
    end.

(* Facilitar visibilidade *)

Fixpoint string_to_nat_list {n : nat} (s : StringLang.string n) :=
  match s with 
  | h :: t => (proj1_sig h) :: (string_to_nat_list t)
  | [] => []
  end.

(* Função equivalente para strings *) 

Definition get_string_function (n : nat) (f : nat -> option nat) :=
  fun (s : StringLang.string n)  => 
  match (f (string_to_nat s)) with
  | Some k => Some (nat_to_string n k)
  | None => None
  end.


(** MACROS **)

(** LEMAS E AUXILIARES **)

Lemma Sn_leq_n'_implies_n_leq_n' : forall n n', S n <= n' -> n <= n'.
Proof.
  lia.
Qed.

(* [opt_lbl] IF X ENDS Si GOTO Ai ( 0 <= i <= n) *)


(* TODO: Possivelmente vou ter que tomar cuidado com as labels.
         Preciso garantir que as labels usadas pelas macros auxiliares
         nunca ocorram dentro de p_nat. Uma opção é criar uma nova letra,
         B, onde o programa em nat só usa A 1, A 2, A 3... E o programa
         em strings pode usar B 1, ... B 2 livremente. *)

Definition get_if_ends_macro (n : nat) (opt_lbl : option label)
  (x : variable) : (StringLang.program n).
Proof.
  refine( 
    let fix aux (k : nat) (k_leq_n : k <= n) :=
      ((match k as eq return (k = eq) -> _ with 
    | S n' => fun _ => 
              let statement := 
                 StringLang.IF_ENDS_GOTO x (exist _ k k_leq_n) (Some (A n)) in 
              (StringLang.Instr opt_lbl) statement :: aux n' _
    | 0 =>  fun _ => let statement := 
              StringLang.IF_ENDS_GOTO x (exist _ k k_leq_n) (Some (A n)) in 
              [(StringLang.Instr opt_lbl) statement]
    end) eq_refl )
    in aux (n) (le_n n )).
    + assert (S n' <= n). { rewrite <- e. exact k_leq_n. }
        apply Sn_leq_n'_implies_n_leq_n', H.
Defined.


(** PRINCIPAIS **)

(* [opt_lbl] IF x GOTO l *)

Definition get_if_macro (n : nat) (opt_lbl : option label)
  (x : variable) (l : option label) : (StringLang.program n).
Proof.
  refine( 
    let fix aux (k : nat) (k_leq_n : k <= n) :=
      ((match k as eq return (k = eq) -> _ with 
    | S n' => fun _ => 
              let statement := 
                 StringLang.IF_ENDS_GOTO x (exist _ k k_leq_n) l in 
              (StringLang.Instr opt_lbl) statement :: aux n' _
    | 0 =>  fun _ => let statement := 
              StringLang.IF_ENDS_GOTO x (exist _ k k_leq_n) l in 
              [(StringLang.Instr opt_lbl) statement]
    end) eq_refl )
    in aux (n) (le_n n )).
    + assert (S n' <= n). { rewrite <- e. exact k_leq_n. }
        apply Sn_leq_n'_implies_n_leq_n', H.
Defined.

(* [B0] x <- + 1 *)

(* [B0] IF X ENDS si GOTO Ai    (1 <= i <= n)
        Y <- s1 Y
        GOTO E

   [Ai] X <- X-       }
        Y <- Si+1 Y    } (1 <= i <= n)
        GOTO C1       }

   [An] X <- X-
        Y <- s1 Y
        GOTO B0

   [C1] IF X ENDS Si GOTO Di     (i <= i <= n)
        GOTO E

   [Di] X <- X-       }
        Y <- Si Y      } (i <= i <= n)
        GOTO C1       }                         *)


Definition get_incr_macro (n : nat) (opt_lbl : option label)
  (x : variable) : (StringLang.program n).
Proof.
    refine (
    let if_x_ends_si_goto_ai := get_if_ends_macro n opt_lbl x
    
    in []
    ).
Defined.

(* [opt_lbl] x <- - 1 *)


(* [B0] IF X ENDS si GOTO Ai    (1 <= i <= n) 
        GOTO E

   [Ai] X <- X-       }
        Y <- Si-1 Y    } (i < i <= n)
        GOTO C        }

   [A1] X <- X-
        IF X != 0 GOTO C2
        GOTO E

   [C2] Y <- Sn Y
        GOTO B0

   [C1] IF X ENDS Si GOTO Di     (i <= i <= n)
        GOTO E

   [Di] X <- X-       }
        Y <- Si Y      } (i <= i <= n)
        GOTO C        }                         *)



Definition get_decr_macro (n : nat) (opt_lbl : option label)
  (x : variable)  : (StringLang.program n).
Proof.
Admitted.


Lemma list_eq_last_init : forall {A: Type} (l: list A),
  l <> [] -> exists init last, l = init ++ [last].
Proof.
  intros A l H.
  induction l as [|h t IH].
  - contradiction.
  - destruct t as [|h' t'].
    + exists [], h.  reflexivity.
    + assert (h' :: t' <> []).
      intros falso. inversion falso.
      apply IH in  H0. destruct H0 as [init last].
      destruct last.
      exists (h :: init). exists x. rewrite <- app_comm_cons. f_equal.
      assumption.
Qed.


(** Obter macros. Por enquanto está incompleta, falta definir INCR e o DECR *)

Definition get_str_macro (k : nat) (i_nat : NatLang.instruction) :
  (StringLang.program k) := 
  match i_nat with 
  | NatLang.Instr opt_lbl (NatLang.INCR x) => get_incr_macro k opt_lbl x
  | NatLang.Instr opt_lbl (NatLang.DECR x) =>  get_decr_macro k opt_lbl x
  | NatLang.Instr opt_lbl (NatLang.IF_GOTO x l) => get_if_macro k opt_lbl x l
  end.

