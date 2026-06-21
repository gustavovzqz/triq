From Triq Require NatLang.
From Triq Require StringLang.
From Triq Require Import LanguagesCommon.

From Stdlib Require Import Nat.
From Stdlib Require Import List.
From Stdlib Require Extraction.
From Stdlib Require Import Lia.
Import ListNotations.



(** Conversão de String para Nat *)


(* n = 2
   [0, 1, 2] -> 3 elementos
   [1, 0, 0, 2, 1]
   2 * 3^4 + 1 * 3 *)

Definition string_to_nat (s : StringLang.string) (max_char : nat) :=
  let fix aux l k {struct l} :=
    match l with
    | h :: t => (h + 1) * ((max_char + 1) ^ k) + aux t (S k)
    | [] => 0
    end
  in aux s 0.

(** Conversão de Nat para String *)


(* Função de Incremento *)

Fixpoint incr_string (s : StringLang.string) (max_char : nat) :=
  match s with 
  | h :: t => if (h <? max_char) then (h + 1) :: t
              else 0 :: incr_string t max_char 
  | [] => [0]
  end.


(* Nat para String, basta usar o incremento n vezes *)

Fixpoint nat_to_string (n : nat) (max_char : nat) : (StringLang.string)  :=
    match n with
    | 0 => []
    | S n' => incr_string (nat_to_string n' max_char) max_char
    end.


(* Decrementar String *)

Fixpoint decr_string (s: StringLang.string) (max_char : nat ) : (StringLang.string) :=
match s with 
| [ ]    => []
| h :: t => match t with 
            | [] => if h =? 0 then [] else [h + 1]
            |  _ => if 0 <? h then (h - 1) :: t
            else max_char :: decr_string t max_char
            end
end.

(* Exemplos *)

Compute nat_to_string 11 3.
Compute string_to_nat [2; 1] 3.
