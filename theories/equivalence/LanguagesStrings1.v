(** * Prova de Equivalência do programa dos naturais para o programa de alfabeto com dois dígitos *)

(** O objetivo deste arquivo é provar a equivalência entre o programa dos naturais
    para o programa de strings, no caso especial em que este possui apenas dois
    símbolos.  *)

From Triq Require NatLang.
From Triq Require NatLangProperties.
From Triq Require Import StringLang.
From Triq Require StringLangProperties.
From Triq Require Import LanguagesCommon.
From Triq Require Import LanguagesUtils.
From Coq Require Import Nat.
From Coq Require Import List.
From Coq Require Extraction.
From Coq Require Import Lia.
Import ListNotations.



Definition a : StringLang.alphabet 1.
Proof.
  exists 0. constructor. constructor.
Defined.

Definition b : StringLang.alphabet 1. 
Proof.
  exists 1. constructor. 
Defined.

Section incr_macro.

Variable (x : variable).
Variable (lbl : option label). (* label da instrução original *)
Variable (n : nat). (* n é o valor da maior label que aparece em p_nat *)
Variable (n': nat). (* n' é o valor da maior label que aparece em p_str *)
Variable (k : nat). (* k é o valor da maior variável Z que aparece em p_nat *)
Variable (k': nat). (* k' é o valor da maior variável Z que aparece em p_str *)



Let z := Z (k + k' + 1).
Let aux := Z (k + k' + 2).


Let B  := Some (A (n + n' + 1)).
Let A1 := Some (A (n + n' + 2)).
Let A2 := Some (A (n + n' + 3)).
Let C  := Some (A (n + n' + 4)).
Let D1 := Some (A (n + n' + 5)).
Let D2 := Some (A (n + n' + 6)).
Let K0 := Some (A (n + n' + 7)).
Let K1 := Some (A (n + n' + 8)).
Let K2 := Some (A (n + n' + 9)).
Let goto l := [ ] IF aux ENDS a GOTO l.

Definition incr_macro_1:=
  <{[
      [lbl] aux <- + a;
      [B] IF x ENDS a GOTO A1;
      [ ] IF x ENDS b GOTO A2;
      [ ] z <- + a;
      goto K0;

      [A1] x <- -;
      [  ] z <- + b;
      goto C;

      [A2] x <- -;
      [  ] z <- + a;
      goto B;

      [C] IF x ENDS a GOTO D1;
      [ ] IF x ENDS b GOTO D2;
      goto K0;

      [D1] x <- -;
      [  ] z <- + a;
      goto C;


      [D2] x <- -;
      [  ] z <- + b;
      goto C;

      [K1] z <- -;
      [  ] x <- + a;
      goto K0;

      [K2] z <- -;
      [  ] x <- +b;

      [K0] IF z ENDS a GOTO K1;
      [  ] IF z ENDS b GOTO K2;
      [  ] aux <- -


    ]}>.

End incr_macro.

Compute (StringLang.get (X 0) (incr_macro_1 (X 0) None 0 0 0 0) ([b]) 80).

Section decr_macro.


Variable (x : variable).
Variable (lbl : option label). (* label da instrução original *)
Variable (n : nat). (* n é o valor da maior label que aparece em p_nat *)
Variable (n': nat). (* n' é o valor da maior label que aparece em p_str *)
Variable (k : nat). (* k é o valor da maior variável Z que aparece em p_nat *)
Variable (k': nat). (* k' é o valor da maior variável Z que aparece em p_str *)

Let z := Z (1 + k + k').
Let aux := Z (2 + k + k').

Let B  := Some (A (1  + n + n')).
Let A1 := Some (A (2  + n + n')).
Let A2 := Some (A (3  + n + n')).
Let C  := Some (A (4  + n + n')).
Let C2 := Some (A (5  + n + n')).
Let D1 := Some (A (6  + n + n')).
Let D2 := Some (A (7  + n + n')).
Let K0 := Some (A (8  + n + n')).
Let K1 := Some (A (9  + n + n')).
Let K2 := Some (A (10 + n + n')).

Let goto l := [ ] IF aux ENDS a GOTO l.

Definition decr_macro_1 :=
  <{[
      [lbl] aux <- + a;
      [B] IF x ENDS a GOTO A1;
      [ ] IF x ENDS b GOTO A2;
          goto K0;

      [A2] x <- -;
      [  ] z <- + a;
           goto C;

      [A1] x <- -;
      (* IF X != 0 GOTO C2 *)
      [  ] IF x ENDS a GOTO C2;
      [  ] IF x ENDS b GOTO C2;
           goto K0;

      [C2] z <- + b;
           goto B;

      [C] IF x ENDS a GOTO D1;
      [ ] IF x ENDS b GOTO D2;
          goto K0;

      [D1] x <- -;
      [  ] z <- + a;
           goto C;

      [D2] x <- -;
      [  ] z <- + b;
           goto C;

      [K1] z <- -;
      [  ] x <- + a;
      goto K0;

      [K2] z <- -;
      [  ] x <- +b;

      [K0] IF z ENDS a GOTO K1;
      [  ] IF z ENDS b GOTO K2;
      [  ] aux <- -
    ]}>.

End decr_macro.

Compute (StringLang.get (X 0) (decr_macro_1 (X 0) None 0 0 0 0) ([b; b]) 100).

Section if_macro.

Variable (x : variable).
Variable (lbl : option label).
Variable (l : option label).

Definition if_macro_1 :=
  <{[ [lbl] IF x ENDS a GOTO l;
      [lbl] IF x ENDS b GOTO l
    ]}>.

End if_macro.




Definition max_label_nat (nat_prg : NatLang.program) : nat :=
  let fix get_max_label (l : NatLang.program) (k : nat) : nat :=
      match l with
      | [] => k
      | NatLang.Instr opt_lbl _ :: t =>
          match opt_lbl with
          | None => get_max_label t k
          | Some (A n) =>
              if ltb k n then get_max_label t n
                       else get_max_label t k
          end
      end
  in get_max_label nat_prg 0.

Definition max_z_nat (nat_prg : NatLang.program) : nat :=
  let fix get_max_z (l : NatLang.program) (k : nat) : nat :=
      match l with
      | [] => k
      | NatLang.Instr opt_lbl (NatLang.INCR (Z n))  :: t 
      | NatLang.Instr opt_lbl (NatLang.DECR (Z n))  :: t 
      | NatLang.Instr opt_lbl (NatLang.IF_GOTO (Z n) _ )  :: t 
        => if ltb k n then get_max_z t n
                      else get_max_z t k
      | _ :: t => get_max_z t k
      end
  in get_max_z nat_prg 0.



Definition get_str_macro1 (i_nat : NatLang.instruction) (n n' k k' : nat) := 
  match i_nat with 
  | NatLang.Instr opt_lbl (NatLang.INCR x) => (incr_macro_1 x opt_lbl n n' k k', 9, 2)
  | NatLang.Instr opt_lbl (NatLang.DECR x) =>  (decr_macro_1 x opt_lbl n n' k k', 10, 2)
  | NatLang.Instr opt_lbl (NatLang.IF_GOTO x l) => (if_macro_1 x opt_lbl l, 0, 0)
end.


Definition get_str_prg (nat_prg : NatLang.program) : StringLang.program 1 :=
  let n := max_label_nat nat_prg in
  let k := max_z_nat nat_prg in
  let fix get_str_prg_rec l n' k' :=
  match l with
  | [] => []
  | i_nat :: t => let '(macro, max_n, max_z) := get_str_macro1 i_nat n n' k k' in 
                    macro ++ (get_str_prg_rec t (n' + max_n) (k' + max_z))
  end
  in get_str_prg_rec nat_prg 0 0.

Fixpoint get_equiv_simulated_position p_nat n :=
  match n with
  | S n' => match p_nat with 
            | h :: t => let '(macro, _, _) := get_str_macro1 h 0 0 0 0 in 
                        length macro 
                        + get_equiv_simulated_position t n'
            | []     => 1
            end
  | O    => 0
  end.

Definition equiv_pos 
  (p_nat : NatLang.program)
  (n : nat)
  (p_str : StringLang.program 0)
  (n' : nat) :=
   n' = get_equiv_simulated_position p_nat n.

Definition incr_string1 (s : StringLang.string 1) : (StringLang.string 1) :=
  let fix incr_rec l :=
    match l with
    | [] => [a]
    | h :: t => if (proj1_sig h =? 0) 
                (* h = a *) then b :: t
                (* h = b *) else (a :: (incr_rec t))
    end
  in rev (incr_rec (rev s)).

Compute (incr_string1 [b; b]).
