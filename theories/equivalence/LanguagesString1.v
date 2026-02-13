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

Let z  := Z (k + 1).

Let aux := Z (k + 2).

Let B  := Some (A (n + n' + 1)).
Let A1 := Some (A (n + n' + 2)).
Let A2 := Some (A (n + n' + 3)).
Let C  := Some (A (n + n' + 4)).
Let C2 := Some (A (n + n' + 5)).
Let D1 := Some (A (n + n' + 6)).
Let D2 := Some (A (n + n' + 7)).
Let K0 := Some (A (n + n' + 8)).
Let K1 := Some (A (n + n' + 9)).
Let K2 := Some (A (n + n' + 10)).
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


Definition max := PeanoNat.Nat.max.

(** Função Auxiliar para Lidar com options *)
Definition max_opts opt_lbl goto_lbl k :=
match opt_lbl, goto_lbl with
| Some (A n), Some (A n') => max (max n n') k 
| Some (A n), None => max n k
| None, Some (A n') => max n' k
| None, None => k
end.

(** Para obter a maior label presente no programa dos naturais, 
  percorremos tanto as labels da instrução (que ocorrem à esquerda) 
  como as labels ALVO, que ocorrem dentro do IF_GOTO *)

Fixpoint get_max_label (l : NatLang.program) (k : nat) : nat :=
    match l with
    | [] => k
    | NatLang.Instr opt_lbl (NatLang.IF_GOTO _ goto_lbl) :: t =>
          get_max_label t (max_opts opt_lbl goto_lbl k)
    | NatLang.Instr opt_lbl _ :: t =>
        match opt_lbl with
        | None => get_max_label t k
        | Some (A n) => get_max_label t (max n k)
        end
    end.

Definition max_label_nat (nat_prg : NatLang.program) : nat :=
get_max_label nat_prg 0.


(** ** Obtendo a Maior Variável Z em p_nat *)

Fixpoint get_max_z (l : NatLang.program) (k : nat) : nat :=
    match l with
    | [] => k
    | NatLang.Instr opt_lbl (NatLang.INCR (Z n))  :: t 
    | NatLang.Instr opt_lbl (NatLang.DECR (Z n))  :: t 
    | NatLang.Instr opt_lbl (NatLang.IF_GOTO (Z n) _ )  :: t  => get_max_z t (max n k)
    | _ :: t => get_max_z t k
    end.

Definition max_z_nat (nat_prg : NatLang.program) : nat :=
 get_max_z nat_prg 0.


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

(* n' = maior variavel z no em p_str 
 n = max_label_nat 
 k = max_z_nat *)

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

Definition macro_length i :=
length (fst (get_str_macro1 i 0 0 0)).

Definition get_equiv_simulated_position (p_nat : NatLang.program) (n : nat) :=
fold_left
  (fun acc instr => acc + macro_length instr)
  (firstn n p_nat)
0.



Definition equiv_pos 
(p_nat : NatLang.program)
(n : nat)
(p_str : StringLang.program )
(n' : nat) :=
 n' = get_equiv_simulated_position p_nat n.

(** ** Incremento de Strings *)

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
  de posição e a equivalência de estado. *)

Definition snap_equiv
(p_nat    : NatLang.program)
(snap_nat : NatLang.snapshot)
(p_str    : StringLang.program)
(snap_str : StringLang.snapshot) :=
match snap_nat with
| NatLang.SNAP n state_nat => (
    match snap_str with
    | StringLang.SNAP n' state_str =>
    state_equiv state_nat state_str  /\ equiv_pos p_nat n p_str n' /\
    state_str (Z ((max_label_nat p_nat) + 1)) = []
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

(** Para mostrar que o programa em strings está em string 1,
  é útil provar primeiro que a concatenação mantém o alfabeto dos
  programas *)

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

(** Podemos usar o lema anterior para provar que o a função
  get_str_prg_rec resulta em um programa de string 1. *)

Lemma get_str_prg_string_1 : forall p_nat n' n k,
StringLang.program_over  (get_str_prg_rec p_nat n' n k ) 1.
Proof.
  induction p_nat.
  + reflexivity.
  + destruct a0. destruct s; repeat constructor; apply IHp_nat.
Qed.

(** Finalmente, podemos continuar com a prova para o caso da função
  geral get_simulated_program. *)

Lemma simulated_program_string_1 : forall p_nat,
StringLang.program_over (get_simulated_program p_nat) 1.
Proof.
  intros p_nat. apply get_str_prg_string_1.
Qed.

(** Para mostrar que o estado é equivalente, é necessário mostrar também
  que a função de incrementar string mantém a string no mesmo alfabeto. *)

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

(** Usando o lema acima, podemos mostrar que a conversão nat_to_string1 
  gera uma string no alfabeto desejado *)

Lemma equiv_state_string1 : forall s_nat,
StringLang.state_over (get_equiv_state s_nat) 1.
Proof.
  unfold StringLang.state_over. unfold get_equiv_state.
  intros. unfold nat_to_string1. induction (s_nat x).
  + apply I.
  + apply incr_string_over, IHn.
Qed.

(** ** Lemas auxiliares *)


(** * Independente do valor inicial para a maior label
    do programa dos naturais, as macros sempre possuirão
    mesmo tamanho *)


Lemma macros_same_size : forall h n1 n2 n3 n4 n5 n6,
length (fst (get_str_macro1 h n1 n2 n3)) = length (fst (get_str_macro1 h n4 n5 n6)).
Proof.
  intros. destruct h; destruct s; reflexivity.
Qed.

(** * Macro nunca é vazia *)

Lemma macro_never_empty : forall instr n n' k,
  fst (get_str_macro1 instr n n' k) <> [].
Proof.
  intros. destruct instr. simpl. destruct s;
  intros H; discriminate H.
Qed.

(** * Como as definições de posição equivalente estão
    em função do fold_left, é importante construir o
    'get_equiv_simulated_position_cons' para obter o mesmo
    resultado de uma definição recursiva tradiciona *)

Lemma fold_left_add_const :
forall l acc c,
  fold_left
    (fun acc instr => acc + macro_length instr)
    l (acc + c)
  =
  acc +
  fold_left
    (fun acc instr => acc + macro_length instr)
    l c.
Proof.
  induction l as [|h t IH]; intros acc c.
  - simpl. reflexivity.
  - simpl. pose proof (IH acc (c + macro_length h)).
    replace (acc + (c + macro_length h)) with (acc + c + (macro_length h))
    in H. rewrite H. reflexivity.
    lia.
Qed.

Lemma get_equiv_simulated_position_cons :
forall h t i,
  get_equiv_simulated_position (h :: t) (S i) =
  macro_length h +
  get_equiv_simulated_position t i.
Proof.
  intros.
  replace (h :: t) with ([h] ++ t).
  + unfold get_equiv_simulated_position. simpl.
    pose proof (fold_left_add_const (firstn i t)  (macro_length h) 0).
    replace (macro_length h + 0) with (macro_length h) in H by lia.
    exact H.
  + reflexivity.
Qed.

(** * Se não há uma instrução em p_nat na linha i, então
    não há uma instrução em p_str na linha equivalente *)

Lemma nat_nth_implies_none : forall p_nat i a b c,
nth_error p_nat i = None ->
nth_error (get_str_prg_rec p_nat a b c) 
(get_equiv_simulated_position p_nat i) = None.
Proof.
  induction p_nat as [|h t IH]; intros.
  - rewrite nth_error_nil. reflexivity.
  - destruct i.
    + simpl in H. discriminate.
    + simpl in H. unfold get_simulated_program in *. 
      remember (max_label_nat (h :: t)). remember (max_z_nat (h :: t)).
      remember (get_str_macro1 h b0 a0 c). destruct p.
      remember (get_str_macro1 h 0 0 0). destruct p.
      rewrite get_equiv_simulated_position_cons.
      simpl. rewrite <- Heqp. destruct h.
      destruct s; simpl in *;
      injection Heqp; injection Heqp0; intros; subst;
      apply IH, H.
Qed.

(** * Se há uma instrução em p_nat na linha i, então há a 
    macro desta instrução na linha equivalente em p_str *)

Lemma nat_nth_implies_macro' : forall p_nat i instr_nat a b c,
nth_error p_nat i = Some instr_nat ->
exists n n' k t,
skipn (get_equiv_simulated_position p_nat i) (get_str_prg_rec p_nat a b c) =
fst (get_str_macro1 instr_nat n n' k) ++ t.
Proof.
  induction p_nat as [|h t IH]; intros.
  + rewrite nth_error_nil in H. discriminate H.
  + destruct i eqn:E.
    ++ simpl. exists b0, a0, c. simpl in H. inversion H.
       remember (get_str_macro1 instr_nat b0 a0 c). destruct p.
       eauto.
    ++ simpl in H. simpl.
       remember (get_str_macro1 h 0 0 0). destruct p.
       remember (get_str_macro1 h b0 a0 c). destruct p.  
       assert (length l = length l0). 
       { assert (l = fst (get_str_macro1 h 0 0 0)). rewrite <- Heqp. reflexivity.
         assert (l0 = fst (get_str_macro1 h b0 a0 c)). 
         rewrite <- Heqp0. reflexivity. rewrite H0, H1. apply macros_same_size. 
       }
        assert (skipn (length l + get_equiv_simulated_position t n)
        (l0 ++ get_str_prg_rec t (a0 + n1) b0 c)  = skipn 
        (get_equiv_simulated_position t n ) (get_str_prg_rec t (a0 + n1) b0 c)).
        { pose proof (skipn_app (length l + get_equiv_simulated_position t n)
          l0 (get_str_prg_rec t (a0 + n1) b0 c)).
          rewrite H1, H0. 
          assert ((skipn (length l0 + get_equiv_simulated_position t n) l0) = []).
          { apply skipn_all_iff.  lia. }
          rewrite H2. simpl. assert ((length l0 + 
          get_equiv_simulated_position t n - length l0) = 
          get_equiv_simulated_position t n) by lia.
          rewrite H3. reflexivity.
        } rewrite get_equiv_simulated_position_cons.
          unfold macro_length. rewrite <- Heqp. simpl.
        rewrite H1.  subst. apply IH, H.
Qed.

Lemma nil_equals_ht_implies_nil : 
  forall A (h : list A) t, 
  [] = h ++ t -> h = [].
Proof.
  intros. destruct h.
  + reflexivity.
  + simpl in H. discriminate H.
Qed.

Lemma nat_nth_implies_macro : forall p_nat i instr_nat,
nth_error p_nat i = Some instr_nat ->
exists n n' k t,
skipn (get_equiv_simulated_position p_nat i) (get_simulated_program p_nat) =
fst (get_str_macro1 instr_nat n n' k) ++ t.
Proof.
  unfold get_simulated_program. intros.
  apply nat_nth_implies_macro', H.
Qed.


(* TODO: Decomposição precisa dizer que n' >=
         max_label h. Provavelmente é melhor obter
         diretamente do nth_error_implies_macro *)

Lemma simulated_program_decomposition :
forall p_nat i instr_nat,
nth_error p_nat i = Some instr_nat ->
exists n n' k h t,
get_simulated_program p_nat =
  h ++ fst (get_str_macro1 instr_nat n n' k) ++ t /\
length h = get_equiv_simulated_position p_nat i.
Proof.
  intros p_nat i instr_nat Hnth.
  destruct (nat_nth_implies_macro _ _ _ Hnth)
    as [n [n' [k [t Hskip]]]].

  exists n, n', k.

  remember (get_equiv_simulated_position p_nat i) as pos.
  remember (get_simulated_program p_nat) as p_str.

  exists (firstn pos p_str), t. split.
  rewrite <- Hskip. rewrite  (firstn_skipn pos p_str).
  reflexivity.

  - rewrite length_firstn.
    assert (length p_str >= pos).
    { pose proof (PeanoNat.Nat.lt_ge_cases (length p_str) pos).
      destruct H.
      + assert (skipn pos p_str = []).
        apply skipn_all_iff. lia. rewrite H0 in Hskip.
        Search ([] = _ ).

        exfalso.
        assert (fst (get_str_macro1 instr_nat n n' k) = []).
        eapply nil_equals_ht_implies_nil. eauto.
        apply (macro_never_empty instr_nat n n' k), H1.
      + unfold ge. lia. 
    } lia.
Qed.


(** * Incrementar uma string sempre resulta em uma lista não vazia *)

Lemma incr_string_not_empty : forall l, (incr_string1 l) <> [].
Proof.
  intros l. unfold incr_string1. destruct l.
  + intros H. discriminate H.
  + destruct (n =? a); intros H; discriminate H.
Qed.

Lemma state_nat_Sn_implies_non_empty : forall v state_nat state_str n,
state_equiv state_nat state_str ->
state_nat v = S n -> exists h t, state_str v = h :: t.
Proof.
  intros. unfold get_equiv_state in H. 
  remember (state_str v). unfold state_equiv in H.
  assert (state_str v = (nat_to_string1 (state_nat v))).
  { apply H, eq_refl. } rewrite H1, H0 in Heqs.
  simpl in Heqs. destruct s eqn:E.
  + pose proof (incr_string_not_empty (nat_to_string1 n)).
    rewrite Heqs in H2. contradiction.
  + exists n0, s0; reflexivity.
Qed.

Lemma firstn_S_nth_error :
forall (A : Type) (l : list A) n x,
  nth_error l n = Some x ->
  firstn (n + 1) l = firstn n l ++ [x].
Proof.
  induction l as [|h t IH]; intros n x H.
  - rewrite nth_error_nil in H. discriminate.
  - destruct n.
    + simpl in *. inversion H; reflexivity.
    + simpl in *. apply IH in H.
      rewrite H. reflexivity.
Qed.

(** * A posição equivalente da linha (n + 1) é a posição equivalente 
    da linha n adicionada do tamanho da macro que está em n. *)

Lemma get_equiv_simulated_Sn:
forall p_nat n instr, 
  nth_error p_nat n = Some instr ->
  get_equiv_simulated_position p_nat (n + 1) 
  = get_equiv_simulated_position p_nat n + macro_length instr.
Proof.
  intros p_nat n instr Hnth.
  unfold get_equiv_simulated_position.
  rewrite firstn_S_nth_error with (x := instr); auto.
  rewrite fold_left_app. simpl. lia.
Qed.

(** #################### CASO IF ##################### *)

(** ** Noções de Pertencimento de Labels em Programas *)

(** * Funções Auxiliares para Comparação de Labels *)

Definition check_equals_labels_label t1 t2 value :=
  match t1, t2 with
  | Some t1', Some t2' => orb (eqb_lbl t1' value) (eqb_lbl t2' value)
  | Some t1', None => eqb_lbl t1' value
  | None, Some t2' => eqb_lbl t2' value
  | None, None => false
  end.

Definition eqb_opt_label_label opt_label value :=
  match opt_label with 
  | Some lbl => eqb_lbl lbl value
  | None => false
  end.

(** * Label Pertence a Alguma Instrução em p_nat *)

Fixpoint label_in_instr p_nat lbl :=
  match p_nat with
  | [] => false
  | NatLang.Instr opt_lbl _ :: t => if (eqb_opt_label_label opt_lbl lbl)
                                    then true
                                    else label_in_instr t lbl
  end.

(** * Label Pertence a Alguma Instrução em p_str *)

Fixpoint label_in_instr_str p_str lbl :=
  match p_str with
  | [] => false
  | StringLang.Instr opt_lbl _ :: t => if (eqb_opt_label_label opt_lbl lbl)
                                    then true
                                    else label_in_instr_str t lbl
  end.

(** * Label Pertence a Algum IF em p_nat *)

Fixpoint label_in_if p_nat lbl :=
  match p_nat with
  | NatLang.Instr _
    (NatLang.IF_GOTO v l) :: t => if (eqb_opt_label_label l lbl)
                                    then true
                                    else label_in_if t lbl
  | _ :: t => label_in_if t lbl
  | [] => false
  end.

(** * get_labeled_instr de (h :: t) onde h possui a label retorna 0 *)

Lemma get_labeled_instr_head : forall p_nat l s a b c,
get_labeled_instr (get_str_prg_rec (NatLang.Instr (Some l) s :: p_nat) a b c)
(Some l) = 0.
Proof.
  intros. 
  remember (max_label_nat (NatLang.Instr (Some l) s :: p_nat)).
  remember (max_z_nat (NatLang.Instr (Some l) s :: p_nat)).
  simpl. destruct s; simpl; rewrite eqb_lbl_refl; reflexivity.
Qed.

(** * get_max_label retorna um valor maior que o argumento *)

Lemma get_max_label_ge_arg : forall p_nat k, 
get_max_label p_nat k >= k.
Proof.
  unfold max. induction p_nat; intros.
  - simpl. constructor.
  - simpl. destruct a0. destruct s eqn:E.
    + destruct o.
       ++ destruct l. pose proof (PeanoNat.Nat.max_dec n k).
          destruct H; unfold max.
          * rewrite e. pose proof (IHp_nat n).
            assert (n >= k).
            { Search (PeanoNat.Nat.max). unfold ge.
              rewrite PeanoNat.Nat.max_comm in e.
              apply PeanoNat.Nat.max_r_iff in e. exact e. }
            eapply PeanoNat.Nat.le_trans.
            ** apply H0.
            ** apply H.
          * rewrite e. apply IHp_nat.
       ++ apply IHp_nat.
  + destruct o.
       ++ destruct l. pose proof (PeanoNat.Nat.max_dec n k).
          destruct H; unfold max.
          * rewrite e. pose proof (IHp_nat n).
            assert (n >= k).
            { Search (PeanoNat.Nat.max). unfold ge.
              rewrite PeanoNat.Nat.max_comm in e.
              apply PeanoNat.Nat.max_r_iff in e. exact e. }
            eapply PeanoNat.Nat.le_trans.
            ** apply H0.
            ** apply H.
          * rewrite e. apply IHp_nat.
       ++ apply IHp_nat.
    + unfold max_opts. destruct o.
       ++ destruct l. destruct o0.
          * destruct l. 
              pose proof (IHp_nat (max (max n n0) k)).
              eapply PeanoNat.Nat.le_trans with (max (max n n0) k).
              { unfold max. lia. }
              apply IHp_nat.
          * pose proof (IHp_nat (max n k)).
            pose proof (PeanoNat.Nat.max_dec n k).
            destruct H0.
            ** unfold max in *. rewrite e in *.
               assert (n >= k).
              { Search (PeanoNat.Nat.max). unfold ge.
              rewrite PeanoNat.Nat.max_comm in e.
              apply PeanoNat.Nat.max_r_iff in e. exact e. }
              eapply PeanoNat.Nat.le_trans.
              *** apply H0.
              *** apply IHp_nat.
            ** unfold max. rewrite e. apply IHp_nat.
       ++ destruct o0.
          * destruct l.
              pose proof (IHp_nat (max n k)).
              pose proof (PeanoNat.Nat.max_dec n k).
              destruct H0.
            ** assert (n >= k).
              { Search (PeanoNat.Nat.max). unfold ge.
              rewrite PeanoNat.Nat.max_comm in e.
              apply PeanoNat.Nat.max_r_iff in e. exact e. }
              eapply PeanoNat.Nat.le_trans.
              *** apply H0.
              *** unfold max. rewrite e. apply IHp_nat.
            ** unfold max. rewrite e. apply IHp_nat.
          * apply IHp_nat.
Qed.

(** * Caso específico do lema anterior *)

Lemma get_max_label_ge_max: forall p_nat k n,
get_max_label p_nat (max k n) >= k.
Proof.
  intros.
  remember (max k n).
  pose proof (get_max_label_ge_arg p_nat n0).
  assert (n0 >= k).
  {Search (PeanoNat.Nat.max _). rewrite Heqn0. unfold max.
   unfold ge. apply PeanoNat.Nat.le_max_l. }
    eapply PeanoNat.Nat.le_trans.
    + apply H0.
    + apply H.
Qed.

(** * get_max_label retorna um valor maior que ou igual
    a qualquer label que está dentro de p_nat *)

Lemma get_max_label_ge_label_in: forall p_nat label_nat k b0,
label_in_instr p_nat label_nat = true ->
label_nat = A b0 ->
get_max_label p_nat k >= b0.
Proof.
  induction p_nat; intros.
  - simpl in H. discriminate.
  - destruct a0. destruct o eqn:E. simpl in H.
    (* o = Some l *)
    + destruct (eqb_lbl l label_nat) eqn:label_eq.
      ++ rewrite lbl_eqb_eq in label_eq. subst. clear H.
         destruct s; unfold max_label_nat.
         +++ simpl. apply get_max_label_ge_max.
         +++ simpl. apply get_max_label_ge_max.
         +++ simpl. destruct o eqn:Eo.
             * destruct l. unfold max. 
               apply PeanoNat.Nat.le_trans with (PeanoNat.Nat.max b0 n).
               { lia. }
               apply get_max_label_ge_max.
             * apply get_max_label_ge_max.
      ++ destruct label_nat. unfold max_label_nat. destruct s.
         +++ destruct l. simpl. apply IHp_nat with (A b0).
              destruct H0. apply H. reflexivity.
         +++ destruct l. simpl. apply IHp_nat with (A b0).
              destruct H0. apply H. reflexivity.
         +++ destruct l. simpl. destruct o0.
             * destruct l. simpl in *.
               destruct (n1 =? n) eqn:E1.
               ** injection H0 as H1. assert (n1 = b0). 
                  { rewrite PeanoNat.Nat.eqb_eq in E1. lia. }
                  subst. apply PeanoNat.Nat.le_trans with (max n0 b0).
                  { unfold max. lia. }
                  apply get_max_label_ge_max.
               ** apply IHp_nat with (A n); auto.
             * apply IHp_nat with (A n); auto.
    (* o = None *)
    + destruct s.
      ++ simpl in *. apply IHp_nat with (label_nat); auto.
      ++ simpl in *. apply IHp_nat with (label_nat); auto.
      ++ simpl in *. destruct o0.
         +++ destruct l. subst. simpl in H. 
             destruct (n =? b0) eqn:E.
             * rewrite PeanoNat.Nat.eqb_eq in E. subst.
               apply get_max_label_ge_max.
             * apply IHp_nat with (A b0); auto.
         +++ apply IHp_nat with label_nat; auto.
Qed.

(** * Caso específico do lema anterior *)

Lemma max_label_plus_one_diff_label_in : forall p_nat label_nat b0 m k,
label_in_instr p_nat label_nat = true ->
label_nat = A b0 ->
k >= max_label_nat p_nat ->
m <> 0 ->
k + m =? b0 = false.
Proof.
  intros.
  assert (max_label_nat p_nat >= b0).
  { unfold max_label_nat. apply get_max_label_ge_label_in with (A b0); auto. rewrite <- H0.
    apply H. }
  rewrite PeanoNat.Nat.eqb_neq.
  assert (k >= b0) by lia. 
  lia.
Qed.

Lemma  max_label_n_k : forall p n k,
n >= k ->
get_max_label p n >= get_max_label p k.
Proof.
  induction p; intros. 
  - simpl. lia.
  - destruct a0. destruct s; simpl.
    + destruct o.
      ++ destruct l. pose proof (PeanoNat.Nat.max_dec n0 k).
         destruct H0.
         +++ unfold max in *. rewrite e. apply IHp. lia.
         +++ unfold max in *. rewrite e. assert (PeanoNat.Nat.max n0 n = n) by lia.
             rewrite H0. apply IHp. lia.
      ++ apply IHp, H.
    + destruct o.
      ++ destruct l. pose proof (PeanoNat.Nat.max_dec n0 k).
         destruct H0.
         +++ unfold max in *. rewrite e. apply IHp. lia.
         +++ unfold max in *. rewrite e. assert (PeanoNat.Nat.max n0 n = n) by lia.
             rewrite H0. apply IHp. lia.
      ++ apply IHp, H.
    + destruct o.
      ++ unfold max_opts. destruct l. destruct o0. 
         +++ destruct l. apply IHp. unfold max. lia.
         +++ apply IHp. unfold max. lia.
      ++ simpl. destruct o0. 
         +++ destruct l. pose proof (PeanoNat.Nat.max_dec n0 k). destruct H0;
             unfold max in *; rewrite e; apply IHp; lia.
         +++ apply IHp, H.
Qed.

Lemma max_label_nat_ht_ge_t : forall h t,
max_label_nat (h :: t) >= max_label_nat t.
Proof.
  intros. unfold max_label_nat. destruct h.
  destruct s.
  + simpl. destruct o.
    ++ destruct l.  rewrite PeanoNat.Nat.max_0_r.
       apply max_label_n_k. lia.
    ++ constructor.
  + simpl. destruct o.
    ++ destruct l.  rewrite PeanoNat.Nat.max_0_r.
       apply max_label_n_k. lia.
    ++ constructor.
  + simpl. destruct o0.
    ++ destruct l. unfold max_opts. destruct o.
       +++ destruct l. apply max_label_n_k. lia.
       +++ apply max_label_n_k. lia.
    ++ unfold max_opts. destruct o.
       +++ destruct l. apply max_label_n_k. lia.
       +++  apply max_label_n_k. lia.
Qed.

Lemma ge_add : forall n m k,
n >= k -> n + m >= k.
Proof.
  induction m; intros.
  + rewrite PeanoNat.Nat.add_0_r. apply H.
  + rewrite PeanoNat.Nat.add_comm. simpl. constructor. unfold ge in *.
    rewrite PeanoNat.Nat.add_comm. apply IHm, H.
Qed.

(** * Se uma label ocorre no programa dos naturais, 
    ela ocorre na posição equivalente no programa
    de strings *)

Lemma labels_equiv_position_in :
forall p_nat label a b c,
  label_in_instr p_nat label = true ->
  b >= max_label_nat p_nat ->
  equiv_pos
    p_nat
    (NatLang.get_labeled_instr p_nat (Some label))
    (get_str_prg_rec p_nat a b c)
    (get_labeled_instr
       (get_str_prg_rec p_nat a b c)
       (Some label)).
Proof.
  induction p_nat as [|h t]; intros.
  - unfold label_in_instr in H. discriminate H.
  - unfold equiv_pos in *. simpl. unfold NatLang.eq_inst_label.
    destruct h. destruct o eqn:E.
    + simpl in H. simpl. destruct s eqn:statement.
      ++ simpl. destruct (eqb_lbl l label) eqn:label_eq.
         * unfold get_equiv_simulated_position. reflexivity.
         * destruct label. rewrite get_equiv_simulated_position_cons. simpl.
           assert ((max_label_nat (NatLang.Instr (Some l) (NatLang.INCR v) 
           :: t) >= max_label_nat t)) by apply max_label_nat_ht_ge_t.
           repeat (erewrite max_label_plus_one_diff_label_in);
           repeat (f_equal); eauto.
           apply IHt; eauto. lia.
           all : apply ge_add; lia.
      ++ simpl. destruct (eqb_lbl l label) eqn:label_eq.
         * unfold get_equiv_simulated_position. reflexivity.
         * destruct label. rewrite get_equiv_simulated_position_cons. simpl.
           assert ((max_label_nat (NatLang.Instr (Some l) (NatLang.DECR v) 
           :: t) >= max_label_nat t)) by apply max_label_nat_ht_ge_t.
           repeat (erewrite max_label_plus_one_diff_label_in);
           repeat (f_equal); eauto.
           apply IHt; eauto. lia.
           all : apply ge_add; lia.
      ++ simpl. destruct (eqb_lbl l label) eqn:label_eq.
         * unfold get_equiv_simulated_position. reflexivity.
         * destruct o0.
           ** simpl. rewrite get_equiv_simulated_position_cons. simpl.
              f_equal. f_equal. unfold eqb_lbl in *.  destruct l.
              destruct l0. destruct label. simpl in *.
              *** apply IHt; eauto. 
                   assert ((max_label_nat ((NatLang.Instr (Some (A n)) 
                   (NatLang.IF_GOTO v (Some (A n0))))
                   :: t) >= max_label_nat t)) by apply max_label_nat_ht_ge_t.
                   lia.
           ** simpl. rewrite get_equiv_simulated_position_cons. simpl.
              f_equal. f_equal. unfold eqb_lbl in *.  destruct l.
              destruct label. simpl in *.
              *** apply IHt; eauto. 
                   assert ((max_label_nat (NatLang.Instr (Some (A n)) 
                   (NatLang.IF_GOTO v None)
                   :: t) >= max_label_nat t)) by apply max_label_nat_ht_ge_t.
                   lia.
    + simpl in H. simpl. destruct s.
      ++ simpl. destruct label. rewrite get_equiv_simulated_position_cons.
         assert ((max_label_nat (NatLang.Instr (None ) (NatLang.INCR v)
         :: t) >= max_label_nat t)) by apply max_label_nat_ht_ge_t.
         simpl. repeat (erewrite max_label_plus_one_diff_label_in);
         repeat (f_equal); eauto; lia.
      ++ simpl. destruct label. rewrite get_equiv_simulated_position_cons.
         assert ((max_label_nat (NatLang.Instr (None ) (NatLang.DECR v)
         :: t) >= max_label_nat t)) by apply max_label_nat_ht_ge_t.
         simpl. repeat (erewrite max_label_plus_one_diff_label_in);
         repeat (f_equal); eauto; lia.
      ++ simpl. destruct label. rewrite get_equiv_simulated_position_cons.
         assert ((max_label_nat (NatLang.Instr (None ) (NatLang.IF_GOTO v o0)
         :: t) >= max_label_nat t)) by apply max_label_nat_ht_ge_t.
         simpl. repeat (erewrite max_label_plus_one_diff_label_in);
         repeat (f_equal); eauto.
         apply IHt; auto; lia.
Qed.

Lemma eq_inst_label_none : forall inst,
NatLang.eq_inst_label inst None = false.
Proof.
  intros instr. destruct instr. 
  simpl. destruct o; reflexivity.
Qed.

(** * get_labeled_instr None termima o programa nos dois casos *)

Lemma labels_equiv_position_none:
forall p_nat a b c,
  equiv_pos
    p_nat
    (NatLang.get_labeled_instr p_nat (None))
    (get_str_prg_rec p_nat a b c)
    (get_labeled_instr
       (get_str_prg_rec p_nat a b c)
       (None)).
Proof.
  induction p_nat; intros. 
  - reflexivity.
  - simpl. rewrite eq_inst_label_none. destruct a0. unfold equiv_pos.
    destruct o; destruct s; rewrite get_equiv_simulated_position_cons;
    simpl; repeat f_equal; apply IHp_nat.
Qed.

(** * get_max_label retorna um valor maior do que ou igual
    a qualquer label que esteja em um if *)

Lemma max_label_ge_label_in_if: forall p_nat label_nat k b0,
label_in_if p_nat label_nat = true ->
label_nat = A b0 ->
get_max_label p_nat k >= b0.
Proof.
  induction p_nat; intros.
  - simpl in H. discriminate.
  - destruct a0. destruct o eqn:E. simpl in H.
    + destruct s.
      ++ simpl. destruct l. apply IHp_nat with label_nat; auto.
      ++ simpl. destruct l. apply IHp_nat with label_nat; auto.
      ++ destruct o0.
         +++ simpl in H. destruct (eqb_lbl l0 label_nat) eqn:E1. 
             * unfold eqb_lbl in *. destruct l0. destruct label_nat.
               rewrite PeanoNat.Nat.eqb_eq in E1. injection H0 as H1.
               subst. simpl. destruct l.
               apply PeanoNat.Nat.le_trans with (max (max n b0) k).
               ** unfold max. lia. 
               ** apply get_max_label_ge_arg. 
             * simpl. destruct l. destruct l0. 
               apply IHp_nat with label_nat; auto.
         +++ simpl in *. destruct l. apply IHp_nat with label_nat; auto.
    + destruct s.
      ++ simpl. apply IHp_nat with label_nat; auto.
      ++ simpl.  apply IHp_nat with label_nat; auto.
      ++ destruct o0.
         +++ simpl in H. destruct (eqb_lbl l label_nat) eqn:E1. 
             * unfold eqb_lbl in *. destruct l. destruct label_nat.
               rewrite PeanoNat.Nat.eqb_eq in E1. injection H0 as H1.
               subst. simpl. 
               apply PeanoNat.Nat.le_trans with (max  b0 k).
               ** unfold max. lia.
               ** apply get_max_label_ge_arg. 
             * simpl. destruct l. apply IHp_nat with label_nat; auto.
         +++ simpl in *. apply IHp_nat with label_nat; auto.
Qed.


(* * caso especifico do lema anterior *)

Lemma max_label_plus_one_diff_if_label: forall p_nat label_nat b0 m k,
label_in_if p_nat label_nat = true ->
label_nat = A b0 ->
k >= max_label_nat p_nat ->
m <> 0 ->
k + m =? b0 = false.
Proof.
  intros.
  assert (max_label_nat p_nat >= b0).
  { unfold max_label_nat. eapply max_label_ge_label_in_if; eauto. }
  rewrite PeanoNat.Nat.eqb_neq.
  assert (k >= b0) by lia. 
  lia.
Qed.


Lemma label_in_instr_cons : forall h t n,
label_in_instr (h :: t) (A n) = false ->
label_in_instr t (A n) = false.
Proof.
  intros.  destruct h. simpl in *. 
  destruct (eqb_opt_label_label o (A n)); auto.
  discriminate H.
Qed.

Lemma label_not_in_implies_out :
forall p_nat label,
  label_in_instr p_nat label = false ->
  NatLang.get_labeled_instr p_nat (Some label) = length p_nat.
Proof.
  induction p_nat as [|h t]; intros.
  + reflexivity.
  + destruct h. simpl in H. 
    assert ((eqb_opt_label_label o label) = false).
    { destruct o. simpl in H. destruct (eqb_lbl l label) eqn:E.
      discriminate H. simpl. apply E. reflexivity. }
    destruct o. rewrite H0 in *. simpl in H0.
    destruct s.
    ++ simpl. rewrite H0. f_equal. apply IHt; auto.
    ++ simpl. rewrite H0. f_equal. apply IHt; auto.
    ++ simpl. rewrite H0. f_equal. apply IHt; auto.
    ++ rewrite H0 in H. simpl. f_equal. apply IHt; auto.
Qed.

Lemma label_not_in_implies_out_str :
forall p_str label,
  label_in_instr_str p_str label = false ->
  get_labeled_instr p_str (Some label) = length p_str.
Proof.
  induction p_str as [|h t]; intros.
  + reflexivity.
  + destruct h. simpl in H. 
    assert ((eqb_opt_label_label o label) = false).
    { destruct o. simpl in H. destruct (eqb_lbl l label) eqn:E.
      discriminate H. simpl. apply E. reflexivity. }
    destruct o. rewrite H0 in *. simpl in H0.
    destruct s.
    ++ simpl. rewrite H0. f_equal. apply IHt; auto.
    ++ simpl. rewrite H0. f_equal. apply IHt; auto.
    ++ simpl. rewrite H0. f_equal. apply IHt; auto.
    ++ rewrite H0 in H. simpl. f_equal. apply IHt; auto.
Qed.

Lemma label_in_implies_max : forall p_nat n k,
label_in_if p_nat (A n) = true ->
get_max_label p_nat k >= n.
Proof.
  induction p_nat; intros.
  - simpl in H. discriminate H.
  - destruct a0. destruct s.
    + simpl in *.  destruct o.
      ++ destruct l. apply IHp_nat, H.
      ++ apply IHp_nat, H.
    + simpl in *.  destruct o.
      ++ destruct l. apply IHp_nat, H.
      ++ apply IHp_nat, H.
    + simpl in H. destruct (eqb_opt_label_label o0 (A n)) eqn:E.
      ++ unfold max_opts. destruct o0.
         +++ simpl in E. destruct l. simpl in E.
             rewrite PeanoNat.Nat.eqb_eq in E. subst.
             simpl. unfold max_opts. destruct o.
             * destruct l. 
               pose proof (get_max_label_ge_arg p_nat (max (max n0 n) k)).
               apply PeanoNat.Nat.le_trans with (max (max n0 n) k ).
               { unfold max. lia. } apply H0.
             * apply get_max_label_ge_max. 
         +++ simpl in E. discriminate E.
      ++ simpl. apply IHp_nat, H.
Qed.

Lemma Nat_add_ge_neq :
forall k n m l,
  k >= n ->
  m + l >= 1 ->
  (k + m + l=? n) = false.
Proof.
  intros. rewrite PeanoNat.Nat.eqb_neq.
  lia.
Qed.

Lemma nth_error_implies_label_in_if :
forall p_nat pos_nat v l o,
  nth_error p_nat pos_nat =
    Some (NatLang.Instr o (NatLang.IF_GOTO v (Some l))) ->
  label_in_if p_nat l = true.
Proof.
  induction p_nat as [| h t IH]; intros pos_nat v l o Hnth.
  - (* lista vazia *)
    rewrite nth_error_nil in Hnth.
    discriminate Hnth.

  - (* h :: t *)
    simpl.
    destruct pos_nat as [| pos'].
    + simpl in Hnth. inversion Hnth; subst.
      simpl. unfold eqb_opt_label_label.
      rewrite eqb_lbl_refl.
      reflexivity.
    + (* pos_nat = S pos' *)
      simpl in Hnth.
      apply IH in Hnth.
      destruct h. destruct s; auto.
      destruct (eqb_opt_label_label o1 l); auto.
Qed.

Lemma label_in_p_nat_implies_not_in_if :
forall p_nat n k a1 a2 a3,
a2 >= get_max_label p_nat k ->
label_in_instr p_nat (A n) = false ->
n <= get_max_label p_nat k ->
label_in_instr_str (get_str_prg_rec p_nat a1 a2 a3) (A n) = false.
Proof.
  induction p_nat; intros.
  - reflexivity.
  - destruct a0. unfold max_label_nat in *. destruct o.
    + destruct s.
      ++ destruct l. simpl in *. destruct (n0 =? n).
         +++ discriminate H0.
         +++ unfold max_label_nat. simpl.
             repeat (rewrite (Nat_add_ge_neq)); auto.
             eapply IHp_nat. apply H. apply H0.
             apply H1. all : lia.
      ++ destruct l. simpl in *. destruct (n0 =? n).
         +++ discriminate H0.
         +++ unfold max_label_nat. simpl.
             repeat (rewrite (Nat_add_ge_neq)); auto.
             eapply IHp_nat. apply H. apply H0.
             apply H1. all : lia.
      ++ destruct l. simpl in *. destruct (n0 =? n).
         +++ discriminate H0.
         +++ unfold max_label_nat. simpl.
             repeat (rewrite (Nat_add_ge_neq)); auto.
             eapply IHp_nat. apply H. apply H0.
             apply H1. all : lia.
    + unfold max_label_nat in *. simpl in *. destruct s.
      ++ simpl in *. repeat (rewrite (Nat_add_ge_neq)); auto.
         eapply IHp_nat. apply H. apply H0.
         apply H1. all : lia.
      ++ simpl in *. repeat (rewrite (Nat_add_ge_neq)); auto.
         eapply IHp_nat. apply H. apply H0.
         apply H1. all : lia.
      ++ simpl in *. repeat (rewrite (Nat_add_ge_neq)); auto.
         eapply IHp_nat. apply H. apply H0.
         apply H1. all : lia.
Qed.

Lemma length_equiv_pos : forall p_nat a b c,
equiv_pos p_nat (length p_nat) 
          (get_str_prg_rec p_nat a b c)
          (length (get_str_prg_rec p_nat a b c)).
Proof.
  induction p_nat; intros; unfold equiv_pos.
  - reflexivity.
  - destruct a0. destruct s; simpl; rewrite get_equiv_simulated_position_cons.
    + simpl. repeat f_equal. apply IHp_nat.
    + simpl. repeat f_equal. apply IHp_nat.
    + simpl. repeat f_equal. apply IHp_nat.
Qed.

Lemma equiv_position_if_not_in : forall p_nat o v l pos_nat,
nth_error p_nat pos_nat = 
Some (NatLang.Instr o (NatLang.IF_GOTO v (Some l))) ->
label_in_instr p_nat l = false ->
equiv_pos p_nat (NatLang.get_labeled_instr p_nat (Some l))
(get_simulated_program p_nat)
(get_labeled_instr (get_simulated_program p_nat) (Some l)).
Proof.
  unfold equiv_pos. intros.
  rewrite label_not_in_implies_out.
  rewrite label_not_in_implies_out_str.
  apply length_equiv_pos. unfold get_simulated_program. destruct l.
  eapply  label_in_p_nat_implies_not_in_if.
  unfold max_label_nat. constructor. apply H0.
  apply label_in_implies_max. eapply nth_error_implies_label_in_if.
  apply H. apply H0.
Qed.


(** Definições de Estado Inicial *)
Definition is_initial_state (state_nat : NatLang.state) :=
state_nat Y = 0 /\ forall n, state_nat (Z n) = 0.


(** get_equiv_state retorna um estado onde state_str (Z n) = 0 *)

Lemma get_equiv_state_initial : forall state_nat,
is_initial_state state_nat ->
forall n, (get_equiv_state state_nat) (Z n) = [].
Proof.
  intros. unfold is_initial_state in H. unfold get_equiv_state.
  destruct H. rewrite H0. reflexivity.
Qed.


(** CASO X <- X + 1 *)

(** ** 1. Do começo da macro, existe um m tal que:
  a) Terminamos a execução na linha da label K0 e;
  b) O valor de Z é o incremento do X inicial e o valor de X é zero. *)

Lemma get_labeled_instr_app :
  forall l1 l2 lbl,
  label_in_instr_str l1 lbl = false ->
  get_labeled_instr (l1 ++ l2) (Some lbl)
  =
  length l1 + get_labeled_instr l2 (Some lbl).
Proof.
  induction l1; intros.
  - simpl. reflexivity.
  - simpl. simpl in H. destruct a0.
    destruct (eqb_opt_label_label o lbl) eqn:E.
    + discriminate H.
    + simpl. destruct o.
      ++ simpl in *. rewrite E. f_equal. apply IHl1, H.
      ++ simpl in *.  f_equal. apply IHl1, H.
Qed.


(* Vai mudar, vou usar o fato de que p_str = h ++ macro ++ t e que
   as labels que ocorrem em macro (exceto a da instrução principal)
   não ocorrem em H. *)


(* TODO: Preciso que a decomposição diga que n' >= max_label_str h *)

Lemma labels_of_macro_not_in_prefix :
  forall p_nat i instr_nat a b c
         n n' k h t lbl o s,

  nth_error p_nat i = Some (NatLang.Instr o s) ->

  get_str_prg_rec p_nat a b c =
      h ++ fst (get_str_macro1 instr_nat n n' k) ++ t ->

  label_in_instr_str
     (fst (get_str_macro1 instr_nat n n' k))
     lbl = true ->

  Some lbl <> o -> 

  label_in_instr_str h lbl = false.
Proof.
Admitted.

(** ** 2. Da linha da label K0, existe um m' tal que:
  a) Terminamos a execução na linha final;
  b) O valor de X é o valor inicial de Z e o valor de Z é 0. *)

Lemma incr_macro_simulates :
  forall p_nat p_str pos_nat state_nat pos_str state_str o x,

  (* Snapshots iniciais são equivalentes *)
  snap_equiv p_nat (NatLang.SNAP pos_nat state_nat)
             p_str (StringLang.SNAP pos_str state_str) ->

  (* p_str simula p_nat *)
  p_str = get_simulated_program p_nat ->

  (* Instrução de p_nat em pos_nat é de incremento *)
  nth_error p_nat pos_nat = Some (NatLang.Instr o (NatLang.INCR x)) ->

  (* Existe um número de passos em p_str, que:
     1. Andamos macro_length e
     2. O estado final possui Z = 0, X = X + 1 (em string) e o resto inalterado. *)

  exists m, snap_equiv p_nat (NatLang.SNAP (pos_nat + 1) (NatLang.incr state_nat x))
                       p_str (compute_program p_str (SNAP pos_str state_str) m).
Proof.
  intros. unfold snap_equiv in H. destruct H as [H2 [H3 H4]].
  remember (NatLang.Instr o (NatLang.INCR x)) as instr_nat.
  assert (exists n n' k t, skipn pos_str p_str = 
          fst (get_str_macro1 instr_nat n n' k) ++ t).
  { rewrite H0, H3. apply nat_nth_implies_macro; auto. }
  destruct H as [n [n' [k [t]]]]. rewrite Heqinstr_nat in H. 

  exists 10. simpl. simpl in H.

  (* Preciso de um lema fácil que relacione nth_error p_str pos_str
    diretamente com a hipotese H *)
  replace pos_str with (pos_str + 0) by lia.
  rewrite <- nth_error_skipn. rewrite H. simpl.
  remember (Z (k + 2)) as aux.
  (* Andei um passo, adicionei a ao final de aux *)
  rewrite PeanoNat.Nat.add_0_r. 
  rewrite <- nth_error_skipn. rewrite H. simpl.
  (* Para prosseguir, preciso verificar o valor de x *)


  (* Lemas auxiliares que eu preciso.
     1. Dizer que  (get_labeled_instr p_str (Some (A (n + n' + _))))
        de dentro de uma macro vai retornar
        pos_macro em p_str + quantidade de linhas *)

Admitted.



(** * Teorema Principal *)

Theorem nat_implies_string :
forall (p_nat : NatLang.program)
       (initial_state_nat : NatLang.state),
is_initial_state initial_state_nat ->

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
  intros. exists (get_simulated_program p_nat).
  exists (get_equiv_state initial_state_nat). split.
  { apply simulated_program_string_1. } split.
  { apply equiv_state_string1. }
  intros steps_nat.
  remember (get_simulated_program p_nat) as p_str.
  remember (get_equiv_state initial_state_nat) as initial_state.
  rewrite Heqinitial_state.
  induction steps_nat as [| steps_nat IH].
  (* Caso base: n = 0 *)
  - exists 0. split.
    + apply get_equiv_state_correct.
    + split.
      ++ reflexivity.
      ++ rewrite get_equiv_state_initial; auto.
  (* Passo da indução *)
  - destruct (NatLang.compute_program p_nat (NatLang.SNAP 0 initial_state_nat)
    steps_nat) as [pos_nat state_nat] eqn:snap_nat_eq.
    destruct IH as [steps_str H0]. unfold snap_equiv in H0.
    destruct (StringLang.compute_program p_str (StringLang.SNAP 0 
    (get_equiv_state initial_state_nat)) steps_str) as [pos_str state_str] 
    eqn:snap_str_eq.
    destruct H0 as [H1 [H2 H3]]. 
    cut (exists m : nat,
            snap_equiv p_nat
            (NatLang.compute_program p_nat (NatLang.SNAP 0 initial_state_nat)
            (S steps_nat))
            p_str
            (compute_program p_str (SNAP 0 
            (get_equiv_state initial_state_nat)) (steps_str + m))).
    intros. destruct H0. exists (steps_str + x). apply H0.

    simpl. unfold NatLang.next_step.
    rewrite snap_nat_eq. 
     assert (forall m, compute_program p_str
     (SNAP 0 (get_equiv_state initial_state_nat)) (steps_str + m) = 
     (compute_program p_str  (compute_program p_str
     (SNAP 0 (get_equiv_state initial_state_nat)) steps_str) m)).
     { intros m. rewrite PeanoNat.Nat.add_comm. 
       apply StringLangProperties.compute_program_add.
     } 
     destruct (nth_error p_nat pos_nat) eqn:p_nat_instr.
    + assert (exists (n n' k : nat) (t : list instruction),
             skipn (get_equiv_simulated_position p_nat pos_nat)
             (get_simulated_program p_nat) = 
             fst (get_str_macro1 i n n' k) ++ t).
      { apply nat_nth_implies_macro, p_nat_instr. }
      destruct H4 as [n [n' [k [ t]]]].
      rewrite <- Heqp_str in H4.
      rewrite <- H2 in H4.
      destruct i, s.
      (* x <- x + 1 *)
        ++ assert (exists m : nat, snap_equiv p_nat (NatLang.SNAP (pos_nat + 1) 
           (NatLang.incr state_nat v)) p_str 
           (compute_program p_str (SNAP pos_str state_str) m)).
           { eapply incr_macro_simulates; eauto. unfold snap_equiv. auto. }
           destruct H5. exists x. rewrite H0, snap_str_eq. apply H5. 

        ++ admit.
        (* if x != 0 goto a *)
        ++ destruct (state_nat v) eqn:E. 
           (* v = 0 *)
           +++ exists 2. rewrite H0, snap_str_eq. simpl in *. 
               assert ((nth_error p_str pos_str) = (Some [o] (IF v ENDS a GOTO o0))).
               { replace pos_str with (pos_str + 0).
                 rewrite <- nth_error_skipn, H4; reflexivity. lia. }
               rewrite H5. assert (state_str v = []). 
               { apply H1. rewrite E. reflexivity. }
               rewrite H6. simpl.
               assert ((nth_error p_str (pos_str + 1))
               = (Some [o] (IF v ENDS b GOTO o0))).
               { rewrite <- nth_error_skipn, H4. reflexivity. }
               rewrite H7. rewrite H6. simpl. split.
               * apply H1.
               * unfold equiv_pos.
                 pose proof (get_equiv_simulated_Sn p_nat pos_nat _ p_nat_instr).
                 unfold macro_length in H8. simpl in H8. rewrite H8.
                 rewrite <- H2. split.
                 ** lia.
                 ** apply H3.
            (* v = S n *)
           +++ assert (exists h t,  state_str v = h :: t).
               { eapply state_nat_Sn_implies_non_empty, E.
                 apply H1. }
               destruct H5 as [char [string_t]].
               assert (char = 0 \/ char = 1). 
               { admit. } destruct H6.
               (* char = 0 *)
               * exists 1. rewrite H0, snap_str_eq. simpl in *.
               assert ((nth_error p_str pos_str) = (Some [o] (IF v ENDS a GOTO o0))).
               { replace pos_str with (pos_str + 0).
                 rewrite <- nth_error_skipn, H4. reflexivity. lia. }
               rewrite H7. rewrite H5, H6. simpl. split.
               ** apply H1.
               ** destruct o0.
                  (* GOTO GOTO None E *)
                  *** destruct (label_in_instr p_nat l) eqn:lbl_in.
                      **** rewrite Heqp_str. unfold get_simulated_program.
                           split; auto. apply labels_equiv_position_in. auto. constructor.
                      **** rewrite Heqp_str. split; auto. 
                           eapply equiv_position_if_not_in; eauto.
                  *** rewrite Heqp_str. split; auto. apply labels_equiv_position_none.
              (* char = 1 *)
               * exists 2. rewrite H0, snap_str_eq. simpl in *.
               assert ((nth_error p_str pos_str) = (Some [o] (IF v ENDS a GOTO o0))).
               { replace pos_str with (pos_str + 0).
                 rewrite <- nth_error_skipn, H4. reflexivity. lia. }
               rewrite H7, H5, H6. simpl. 
               assert ((nth_error p_str (pos_str + 1) = (Some [o] (IF v ENDS b GOTO o0)))).
               { rewrite <- nth_error_skipn, H4. reflexivity. }
               rewrite H8, H5, H6. simpl. split.
               ** apply H1.
               ** split; auto. destruct o0.
                  *** destruct (label_in_instr p_nat l) eqn:lbl_in.
                      **** rewrite Heqp_str. unfold get_simulated_program.
                           apply labels_equiv_position_in. auto. constructor.
                      **** rewrite Heqp_str. eapply equiv_position_if_not_in; eauto.
                  *** rewrite Heqp_str. apply labels_equiv_position_none.
      + unfold equiv_pos in H1.
        simpl. exists 0. replace (steps_str + 0) with steps_str.
        rewrite snap_str_eq. split.
        ++ apply H1.
        ++ split; auto.
        ++ lia.
Abort.
