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

(** "a" e "b" são os caracteres básicos do alfabeto de dois dígitos. *)

Definition a  := 0.

Definition b := 1.

(** * Definições das Macros para o Caso de Dois Dígitos *)

(** Diferente do caso "string 0" em que há uma associação direta
    entre as instruções dos naturais com as instruções em strings,
    aqui precisaremos definir macros mais complexas e que precisam
    de variáveis e labels próprias. *)

(** Para lidar com as variáveis auxiliares, basta padronizar o seguinte:
    Seja _k_ o maior valor de _n_ na variável _Z n_ no programa dos naturais.
    Para o programa de strings, sempre usaremos _aux_ como Z (k + 2) e
    _z_ como Z (k + 1). Para usarmos Z de maneira segura, vamos sempre
    zerar o seu valor ao final de cada macro, garantindo que estará
    "limpo" para a execução da próxima macro. A variável aux será
    usada apenas para simular o GOTO, então a argumentação deve
    seguir um caminho um pouco diferente. *)

(** ** Macro Soma Um *)

Section incr_macro.

Variable (x : variable).
Variable (lbl : option label). (* label da instrução original *)
Variable (n : nat). (* n é o valor da maior label que aparece em p_nat *)
Variable (n': nat). (* n' é o valor da maior label que aparece em p_str *)
Variable (k : nat). (* k é o valor da maior variável Z que aparece em p_nat *)

Let z := Z (k + 1).
Let aux := Z (k + 2).


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
      [  ] IF z ENDS b GOTO K2
    ]}>.

End incr_macro.

Compute (StringLang.get (X 0) (incr_macro_1 (X 0) None 0 0 0) ([b]) 80).


(** ** Macro Subtrai Um *)

Section decr_macro.

Variable (x : variable).
Variable (lbl : option label). (* label da instrução original *)
Variable (n : nat). (* n é o valor da maior label que aparece em p_nat *)
Variable (n': nat). (* n' é o valor da maior label que aparece em p_str *)
Variable (k : nat). (* k é o valor da maior variável Z que aparece em p_nat *)

Let z := Z (1 + k).
Let aux := Z (2 + k).

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
      [  ] IF z ENDS b GOTO K2
    ]}>.

End decr_macro.

Compute (StringLang.get (X 0) (decr_macro_1 (X 0) None 0 0 0) ([b; b]) 100).

(** ** Macro IF GOTO *)

Section if_macro.

Variable (x : variable).
Variable (lbl : option label).
Variable (l : option label).

Definition if_macro_1 :=
  <{[ [lbl] IF x ENDS a GOTO l;
      [lbl] IF x ENDS b GOTO l
    ]}>.

End if_macro.

(** * Obtendo as Macros *)

(** Para construir as macro, precisamos de algumas funções auxiliares
    para que possamos obter valores únicos para labels e variáveis
    auxiliares. Assim, podemos ter a garantia de que cada label
    ou variável extra no programa de strings não ocorre no programa
    dos naturais. *)



(** ** Obtendo a Maior Label em p_nat *)

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


(** ** Obtendo a Maior Variável Z em p_nat *)

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


(** ** Obtendo a Macro *)

(** Para obter a macro, precisamos passar:
      - A instrução em p_nat;
      - O índice da maior label em p_nat;
      - O índice da maior variável z em p_nat;
      - O índice da maior label em p_str.

   O último índice será objeto na função recursiva de obter o programa
   simulado. Veja que, como retorno da função, temos tanto a macro resultante
   como o número de labels que a macro utilizou. Com a quantidade de labels,
   conseguimos manter atualizado o valor de k para que as próximas macros
   usem labels inteiramente novas *)


Definition get_str_macro1 (i_nat : NatLang.instruction) (n n' k : nat) := 
  match i_nat with 
  | NatLang.Instr opt_lbl (NatLang.INCR x) => (incr_macro_1 x opt_lbl n n' k , 9)
  | NatLang.Instr opt_lbl (NatLang.DECR x) =>  (decr_macro_1 x opt_lbl n n' k, 10)
  | NatLang.Instr opt_lbl (NatLang.IF_GOTO x l) => (if_macro_1 x opt_lbl l, 0)
end.


(** ** Obtendo o Programa Simulado *)


Fixpoint get_str_prg_rec l n' n k :=
  match l with
  | [] => []
  | i_nat :: t => let (macro, max_n) := get_str_macro1 i_nat n n' k  in 
                    macro ++ (get_str_prg_rec t (n' + max_n) n k)
  end.



Definition get_simulated_program (nat_prg : NatLang.program) : StringLang.program :=
  let n := max_label_nat nat_prg in
  let k := max_z_nat nat_prg in
  get_str_prg_rec nat_prg 0 n k.



(** * Definições para a Equivalência *)

(** Para o teorema principal, falaremos sobre _snapshots_ equivalentes,
    ou seja, snapshots que possuem estados e posições equivalentes. A ideia
    da prova é mostrar, por indução, que sempre há um número de passos no
    programa de strings que mantem a equivalência de snapshot para um passo
    do programa dos naturais.

    Para a equivalência de posição, precisamos de um conceito que nos permita
    raciocinar sobre a execução da instrução e a execução da macro. A ideia é
    que, se a snapshot do programa dos naturais está na linha n com a instrução i,
    então o programa de strings está em uma linha n', _equivalente a n_, obtida ao
    expandir cada macro do programa dos naturais. *)


(** A posição equivalente é simplesmente a soma do tamanho de todas 
    as expansões de macro até aquele ponto. *)

Fixpoint get_equiv_simulated_position p_nat n :=
  match n with
  | S n' => match p_nat with 
            | h :: t => let (macro, _) := get_str_macro1 h 0 0 0 in 
                        length macro 
                        + get_equiv_simulated_position t n'
            | []     => 1
            end
  | O    => 0
  end.

Definition equiv_pos 
  (p_nat : NatLang.program)
  (n : nat)
  (p_str : StringLang.program )
  (n' : nat) :=
   n' = get_equiv_simulated_position p_nat n.


(** O incremento de strings é trivial no que se espera para um número
    na base dois. É importante lembrar que estamos operando sobre uma
    o inverso da string, o que simplifica as operações *)

Fixpoint incr_string1 (s : StringLang.string ) : (StringLang.string ) :=
  match s with
  | h :: t => if h =? a then b :: t
              else a :: incr_string1 t 
  | []     => [b] 
  end.

(** Com a função de incremento, podemos implementar a conversão
    de natural para string utilizando _n_ incrementos. *)

Fixpoint nat_to_string1 n :=
  match n with
  | 0 => []
  | S n' => incr_string1 (nat_to_string1 n')
  end.

(** A noção de equivalência de estados implica que qualquer variável que aparece
    no estado de p_nat deve possuir o mesmo valor no estado de p_str *)

Definition state_equiv (s_nat : NatLang.state) (s_str : StringLang.state) :=
  forall (x : variable) (v : StringLang.string),
  nat_to_string1 (s_nat x) = v -> s_str x = v.

(** Para a noção de equivalência de snapshot, unimos as definições de equivalência
    de posição e a equivaência de estado. *)

Definition snap_equiv
  (p_nat    : NatLang.program)
  (snap_nat : NatLang.snapshot)
  (p_str    : StringLang.program)
  (snap_str : StringLang.snapshot) :=
  match snap_nat with
  | NatLang.SNAP n state_nat => (
      match snap_str with
      | StringLang.SNAP n' state_str =>
      state_equiv state_nat state_str  /\ equiv_pos p_nat n p_str n'
      end)
  end.

(** Para obter um estado equivalente, basta colocar uma máscara no estado 
    dos naturais que converte todo resultado para string. *)

Definition get_equiv_state nat_state : (StringLang.state ) :=
  (fun x => nat_to_string1 (nat_state x)).

(** É trivial provar que a função anterior retorna um estado equivalente
    ao argumento. *)

Lemma get_equiv_state_correct : forall state_nat,
  state_equiv state_nat (get_equiv_state state_nat).
Proof.
  intros state_nat. unfold get_equiv_state. unfold state_equiv.
  intros x v state_x_eq_v. destruct (state_nat x) eqn:E.
  + simpl. rewrite <- state_x_eq_v. reflexivity.
  + rewrite <- state_x_eq_v. reflexivity.
Qed.

Lemma app_string_1 : forall p p', 
  StringLang.program_over p  1  ->
  StringLang.program_over p' 1  ->
  StringLang.program_over (p ++ p') 1.
Proof.
  intros p p' H H0; induction p.
  + simpl. apply H0.
  + simpl. simpl in H. destruct a0. destruct s.
    ++ destruct H; auto.
    ++ apply IHp, H.
    ++ destruct H; auto.
Qed.


Lemma get_str_prg_string_1 : forall p_nat n' n k,
  StringLang.program_over  (get_str_prg_rec p_nat n' n k ) 1.
Proof.
  induction p_nat.
  + reflexivity.
  + destruct a0. destruct s; repeat constructor; apply IHp_nat.
Qed.

Lemma simulated_program_string_1 : forall p_nat,
  StringLang.program_over (get_simulated_program p_nat) 1.
Proof.
  intros p_nat. apply get_str_prg_string_1.
Qed.

Lemma incr_string_over : forall s, 
  StringLang.string_over s 1 ->
  StringLang.string_over (incr_string1 s) 1.
Proof.
  intros. induction s.
  + simpl. repeat (constructor).
  + simpl in *. destruct H. pose proof (IHs H0).
    destruct (a0 =? a).
    ++ repeat constructor. apply H0.
    ++ simpl. repeat constructor. apply H1.
Qed.

Lemma equiv_state_string0 : forall s_nat,
  StringLang.state_over (get_equiv_state s_nat) 1.
Proof.
  unfold StringLang.state_over, StringLang.string_over, get_equiv_state.
  intros. induction (s_nat x).
  + apply I.
  + fold StringLang.string_over in *. simpl.
    destruct (nat_to_string1 n) eqn:E.
    ++ simpl; auto.
    ++ simpl. destruct (n0 =? a) eqn:E1.
       * simpl. simpl in IHn. split.
         ** constructor.
         ** apply IHn.
       * simpl in *. split.
         ** repeat constructor.
         ** apply incr_string_over, IHn.
Qed.


Lemma nat_nth_implies_macro : forall p_nat i instr_nat,
  nth_error p_nat i = Some instr_nat ->
  exists t n n' k,
  skipn (get_equiv_simulated_position p_nat i) (get_simulated_program p_nat) =
  fst (get_str_macro1 instr_nat n n' k) ++ t.
Proof.
  induction p_nat; intros; simpl in *.
  + rewrite nth_error_nil in H. discriminate H.
  + destruct i.
    ++ simpl in H. injection H as eq. subst. exists (get_simulated_program p_nat).
Abort.




Theorem nat_implies_string :
  forall (p_nat : NatLang.program)
         (initial_state_nat : NatLang.state),

  exists (p_str : StringLang.program)
         (initial_state_str : StringLang.state),
  StringLang.program_over p_str 1 /\
  StringLang.state_over initial_state_str 1 /\

  forall (n : nat),
  exists (n' : nat),
  snap_equiv p_nat
             (NatLang.compute_program p_nat (NatLang.SNAP 0 initial_state_nat) n)
             p_str
             (StringLang.compute_program p_str (StringLang.SNAP 0 initial_state_str) n').
Proof.
  intros p_nat state_nat. exists (get_simulated_program p_nat). 
  exists (get_equiv_state state_nat). split.
  apply simulated_program_string_1. split.
  apply equiv_state_string0.
  (* prova segue *)


