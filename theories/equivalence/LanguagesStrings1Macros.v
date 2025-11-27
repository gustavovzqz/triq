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


(** * Definições Básicas para a Equivalência *)

(** Diferente do caso string0, não conseguimos nos aproveitar de alguma
    propriedade para construir um algoritmo mais simples de incremento.
    Assim, a função incr_string usada será a genérica, e simplificaremos
    apenas a construção das macros. *)

Definition a : StringLang.alphabet 1.
Proof.
  exists 0. constructor. constructor.
Defined.

Definition b : StringLang.alphabet 1. 
Proof.
  exists 1. constructor. 
Defined.

Section incr_prog.

Let x := X 0.

Let y := Y.
Let z := Z 0.

Let B := Some (A 1).
Let A1 := Some (A 2).
Let A2 := Some (A 3).
Let C := Some (A 4).
Let D1 := Some (A 5).
Let D2 := Some (A 6).
Let E  := Some (A 7).
Let goto l := [ ] IF z ENDS a GOTO l.

(* Para este caso, eu não precisaria do Z0, apenas do Y. *)

Definition incr_prog_1:=
  <{[
      [ ]  z <- + a;
      [B] IF x ENDS a GOTO A1;
      [ ] IF x ENDS b GOTO A2;
      [ ] y <- + a;
      goto E;

      [A1] x <- -;
      [  ] y <- + b;
      goto C;

      [A2] x <- -;
      [  ] y <- + a;
      goto B;

      [C] IF x ENDS a GOTO D1;
      [ ] IF x ENDS b GOTO D2;
      goto E;

      [D1] x <- -;
      [  ] y <- + a;
      goto C;


      [D2] x <- -;
      [  ] y <- + b;
      goto C

    ]}>.
End incr_prog.


Compute (StringLang.get Y incr_prog_1 ([b; b]) 40).

Section decr_prog.

Let x := X 0.
Let y := Y.
Let z := Z 0.

Let B := Some (A 0).
Let A1 := Some (A 1). 
Let A2 := Some (A 2).
Let C := Some (A 3).
Let C2 := Some (A 4).
Let D1 := Some (A 5).
Let D2 := Some (A 6).
Let E := Some (A 7).

Let goto l := [ ] IF z ENDS a GOTO l.

Definition decr_prog_1 :=
  <{[
      [ ] z <- + a;
      [B] IF x ENDS a GOTO A1;
      [ ] IF x ENDS b GOTO A2;
          goto E;

      [A2] x <- -;
      [  ] y <- + a;
           goto C;

      [A1] x <- -;
      (* IF X != 0 GOTO C2 *)
      [  ] IF x ENDS a GOTO C2;
      [  ] IF x ENDS b GOTO C2;
           goto E;

      [C2] y <- + b;
           goto B;

      [C] IF x ENDS a GOTO D1;
      [ ] IF x ENDS b GOTO D2;
          goto E;

      [D1] x <- -;
      [  ] y <- + a;
           goto C;

      [D2] x <- -;
      [  ] y <- + b;
           goto C
    ]}>.

End decr_prog.


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


