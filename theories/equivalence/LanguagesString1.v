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

Definition max_opts opt_lbl goto_lbl k :=
  match opt_lbl, goto_lbl with
  | Some (A n), Some (A n') => max (max n n) k 
  | Some (A n), None => max n k
  | None, Some (A n') => max n' k
  | None, None => k
  end.

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

Import ListNotations.

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

Lemma macros_same_size : forall h n1 n2 n3 n4 n5 n6,
  length (fst (get_str_macro1 h n1 n2 n3)) = length (fst (get_str_macro1 h n4 n5 n6)).
Proof.
  intros. destruct h; destruct s; reflexivity.
Qed.


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

Lemma nat_nth_implies_macro : forall p_nat i instr_nat,
  nth_error p_nat i = Some instr_nat ->
  exists n n' k t,
  skipn (get_equiv_simulated_position p_nat i) (get_simulated_program p_nat) =
  fst (get_str_macro1 instr_nat n n' k) ++ t.
Proof.
  unfold get_simulated_program. intros.
  apply nat_nth_implies_macro', H.
Qed.


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


Fixpoint label_in p_nat lbl :=
  match p_nat with
  | [] => false
  | NatLang.Instr opt_lbl _ :: t => match opt_lbl with 
                                    | Some lbl' => if eqb_lbl lbl' lbl then true
                                                  else label_in t lbl
                                    | None => label_in t lbl
                                    end
  end.


Lemma get_labeled_instr_simulated : forall p_nat l s a b c,
  get_labeled_instr (get_str_prg_rec (NatLang.Instr (Some l) s :: p_nat) a b c)
  (Some l) = 0.
Proof.
  intros. 
  remember  (max_label_nat (NatLang.Instr (Some l) s :: p_nat)).
  remember (max_z_nat (NatLang.Instr (Some l) s :: p_nat)).
  simpl. destruct s; simpl; rewrite eqb_lbl_refl; reflexivity.
Qed.



(* Devo ter feito algum destruct errado em algum momento *)
Lemma get_max_label_max' : forall p_nat k, 
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
          * destruct l. rewrite PeanoNat.Nat.max_id.
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

Lemma get_max_label_max : forall p_nat k n,
  get_max_label p_nat (max k n) >= k.
Proof.
  intros.
  remember (max k n).
  pose proof (get_max_label_max' p_nat n0).
  assert (n0 >= k).
  {Search (PeanoNat.Nat.max _). rewrite Heqn0. unfold max.
   unfold ge. apply PeanoNat.Nat.le_max_l. }
    eapply PeanoNat.Nat.le_trans.
    + apply H0.
    + apply H.
Qed.
  

Lemma max_label_gt: forall p_nat label_nat k b0,
  label_in p_nat label_nat = true ->
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
         +++ simpl. apply get_max_label_max.
         +++ simpl. apply get_max_label_max.
         +++ simpl. destruct o.
             * destruct l. unfold max. rewrite PeanoNat.Nat.max_id.
               apply get_max_label_max.
             * apply get_max_label_max.
      ++ destruct label_nat. unfold max_label_nat. destruct s.
         +++  destruct l. simpl. apply IHp_nat with (A b0).
              destruct H0. apply H. reflexivity.
         +++  destruct l. simpl. apply IHp_nat with (A b0).
              destruct H0. apply H. reflexivity.
         +++  destruct l. simpl. apply IHp_nat with (A b0).
              destruct H0. apply H. reflexivity.
    + destruct s.
      ++ simpl in *. apply IHp_nat with (label_nat); auto.
      ++ simpl in *. apply IHp_nat with (label_nat); auto.
      ++ simpl in *. destruct o0.
         +++ destruct l. apply IHp_nat with label_nat; auto.
         +++ apply IHp_nat with label_nat; auto.
Qed.


Lemma max_label_diff_label : forall p_nat label_nat b0 m k,
  label_in p_nat label_nat = true ->
  label_nat = A b0 ->
  k >= max_label_nat p_nat ->
  m <> 0 ->
  k + m =? b0 = false.
Proof.
Admitted.


Lemma max_label_nat_ht_gt_t : forall h t,
  max_label_nat (h :: t) >= max_label_nat t.
Proof.
  intros. unfold max_label_nat. destruct h.
  destruct s.
  + simpl. destruct o.
    ++ destruct l.  rewrite PeanoNat.Nat.max_0_r.
       admit.
    ++ constructor.
  + simpl. destruct o.
    ++ destruct l.  rewrite PeanoNat.Nat.max_0_r.
       admit.
    ++ constructor.
  + simpl. destruct o0.
    ++ destruct l. simpl.
Admitted.

Lemma ge_add : forall n m k,
  n >= k -> n + m >= k.
Proof.
  induction m; intros.
  + rewrite PeanoNat.Nat.add_0_r. apply H.
  + rewrite PeanoNat.Nat.add_comm. simpl. constructor. unfold ge in *.
    rewrite PeanoNat.Nat.add_comm. apply IHm, H.
Qed.

Lemma labels_equiv_position_in :
  forall p_nat label a b c,
    label_in p_nat label = true ->
    b >= max_label_nat p_nat ->
    equiv_pos
      p_nat
      (NatLang.get_labeled_instr p_nat (Some label))
      (get_str_prg_rec p_nat a b c)
      (get_labeled_instr
         (get_str_prg_rec p_nat a b c)
         (Some label)).
Proof.
  induction p_nat; intros.
  - unfold label_in in H. discriminate H.
  - unfold equiv_pos in *. simpl. unfold NatLang.eq_inst_label.
    destruct a0. destruct o eqn:E.
    + simpl in H. simpl. destruct s eqn:statement.
      ++ simpl. destruct (eqb_lbl l label) eqn:label_eq.
         * unfold get_equiv_simulated_position. reflexivity.
         * destruct label. rewrite get_equiv_simulated_position_cons. simpl.
           assert ((max_label_nat (NatLang.Instr (Some l) (NatLang.INCR v) 
           :: p_nat) >= max_label_nat p_nat)) by apply max_label_nat_ht_gt_t.
           repeat (erewrite max_label_diff_label);
           repeat (f_equal); eauto.
           apply IHp_nat; eauto. lia.
           all : apply ge_add; lia.
      ++ simpl. destruct (eqb_lbl l label) eqn:label_eq.
         * unfold get_equiv_simulated_position. reflexivity.
         * destruct label. rewrite get_equiv_simulated_position_cons. simpl.
           assert ((max_label_nat (NatLang.Instr (Some l) (NatLang.DECR v) 
           :: p_nat) >= max_label_nat p_nat)) by apply max_label_nat_ht_gt_t.
           repeat (erewrite max_label_diff_label);
           repeat (f_equal); eauto.
           apply IHp_nat; eauto. lia.
           all : apply ge_add; lia.
      ++ simpl. destruct (eqb_lbl l label) eqn:label_eq.
         * unfold get_equiv_simulated_position. reflexivity.
         * destruct label. rewrite get_equiv_simulated_position_cons. simpl.
           assert ((max_label_nat (NatLang.Instr (Some l) (NatLang.IF_GOTO v o0)
           :: p_nat) >= max_label_nat p_nat)) by apply max_label_nat_ht_gt_t.
           repeat (erewrite max_label_diff_label);
           repeat (f_equal); eauto.
           apply IHp_nat; eauto. lia.
    + simpl in H. simpl. destruct s.
      ++ simpl. destruct label. rewrite get_equiv_simulated_position_cons.
         assert ((max_label_nat (NatLang.Instr (None ) (NatLang.INCR v)
         :: p_nat) >= max_label_nat p_nat)) by apply max_label_nat_ht_gt_t.
         simpl. repeat (erewrite max_label_diff_label);
         repeat (f_equal); eauto; lia.
      ++ simpl. destruct label. rewrite get_equiv_simulated_position_cons.
         assert ((max_label_nat (NatLang.Instr (None ) (NatLang.DECR v)
         :: p_nat) >= max_label_nat p_nat)) by apply max_label_nat_ht_gt_t.
         simpl. repeat (erewrite max_label_diff_label);
         repeat (f_equal); eauto; lia.
      ++ simpl. destruct label. rewrite get_equiv_simulated_position_cons.
         assert ((max_label_nat (NatLang.Instr (None ) (NatLang.IF_GOTO v o0)
         :: p_nat) >= max_label_nat p_nat)) by apply max_label_nat_ht_gt_t.
         simpl. repeat (erewrite max_label_diff_label);
         repeat (f_equal); eauto.
         apply IHp_nat; auto; lia.
Qed.

Lemma labels_equiv_position_not_in:
  forall p_nat label a b c,
    label_in p_nat label = false ->
    b >= max_label_nat p_nat ->
    equiv_pos
      p_nat
      (NatLang.get_labeled_instr p_nat (Some label))
      (get_str_prg_rec p_nat a b c)
      (get_labeled_instr
         (get_str_prg_rec p_nat a b c)
         (Some label)).
Proof.
Admitted.

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
Admitted.



Lemma state_str_1_char_0_1 : forall state_str x h t,
  StringLang.state_over state_str 1 ->
  state_str x = h :: t ->
  h = 0 \/ h = 1.
Proof.
  intros. unfold state_over in H. unfold string_over in H.
  pose proof (H x). rewrite H0 in H1. destruct H1. destruct H0.
  destruct h.
  + left. reflexivity.
  + right. destruct h.
    ++ reflexivity.
    ++ apply le_S_n in H1. apply PeanoNat.Nat.nle_succ_0 in H1.
       contradiction.
Qed.

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
    + destruct p_nat.
      ++ simpl. reflexivity.
      ++ simpl. reflexivity.
  (* Passo da indução *)
  - destruct (NatLang.compute_program p_nat (NatLang.SNAP 0 initial_state_nat)
    steps_nat) as [pos_nat state_nat] eqn:snap_nat_eq.
    destruct IH as [steps_str H]. unfold snap_equiv in H.
    destruct (StringLang.compute_program p_str (StringLang.SNAP 0 
    (get_equiv_state initial_state_nat)) steps_str) as [pos_str state_str] 
    eqn:snap_str_eq.
    destruct H as [H0 H1]. 
    cut (exists m : nat,
            snap_equiv p_nat
            (NatLang.compute_program p_nat (NatLang.SNAP 0 initial_state_nat)
            (S steps_nat))
            p_str
            (compute_program p_str (SNAP 0 
            (get_equiv_state initial_state_nat)) (steps_str + m))).
    intros. destruct H. exists (steps_str + x). apply H.

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
      destruct H2 as [n [n' [k [ t]]]].
      rewrite <- Heqp_str in H2.
      rewrite <- H1 in H2.
      destruct i, s.
      (* x <- x + 1 *)
      ++ admit.
      (* x <- x - 1 *)
      ++ admit.
      (* if x != 0 goto a *)
      ++ destruct (state_nat v) eqn:E. 
         (* v = 0 *)
         +++ exists 2. rewrite H, snap_str_eq. simpl in *. 
             assert ((nth_error p_str pos_str) = (Some [o] (IF v ENDS a GOTO o0))).
             { replace pos_str with (pos_str + 0).
               rewrite <- nth_error_skipn, H2. reflexivity. lia. }
             rewrite H3. assert (state_str v = []). 
             { apply H0. rewrite E. reflexivity. }
             rewrite H4. simpl.
             assert ((nth_error p_str (pos_str + 1))
             = (Some [o] (IF v ENDS b GOTO o0))).
             { rewrite <- nth_error_skipn, H2. reflexivity. }
             rewrite H5. rewrite H4. simpl. split.
             * apply H0.
             * unfold equiv_pos.
               pose proof (get_equiv_simulated_Sn p_nat pos_nat _ p_nat_instr).
               unfold macro_length in H6. simpl in H6. rewrite H6.
               rewrite <- H1. lia.
          (* v = S n *)
         +++ assert (exists h t,  state_str v = h :: t).
             { eapply state_nat_Sn_implies_non_empty, E.
               apply H0. }
             destruct H3 as [char [string_t]].
             assert (char = 0 \/ char = 1). 
             { admit. } destruct H4.
               
             (* char = 0 *)
             * exists 1. rewrite H, snap_str_eq. simpl in *.
             assert ((nth_error p_str pos_str) = (Some [o] (IF v ENDS a GOTO o0))).
             { replace pos_str with (pos_str + 0).
               rewrite <- nth_error_skipn, H2. reflexivity. lia. }
             rewrite H5, H3, H4. simpl. split.
             ** apply H0.
             ** destruct o0.
                *** destruct (label_in p_nat l) eqn:lbl_in.
                    **** rewrite Heqp_str. unfold get_simulated_program.
                         apply labels_equiv_position_in. auto. constructor.
                    **** rewrite Heqp_str. apply labels_equiv_position_not_in.
                         auto. constructor.
                *** rewrite Heqp_str. apply labels_equiv_position_none.
            (* char = 1 *)
             * exists 2. rewrite H, snap_str_eq. simpl in *.
             assert ((nth_error p_str pos_str) = (Some [o] (IF v ENDS a GOTO o0))).
             { replace pos_str with (pos_str + 0).
               rewrite <- nth_error_skipn, H2. reflexivity. lia. }
             rewrite H5, H3, H4. simpl. 
             assert ((nth_error p_str (pos_str + 1) = (Some [o] (IF v ENDS b GOTO o0)))).
             { rewrite <- nth_error_skipn, H2. reflexivity. }
             rewrite H6, H3, H4. simpl. split.
             ** apply H0.
             ** destruct o0.
                *** destruct (label_in p_nat l) eqn:lbl_in.
                    **** rewrite Heqp_str. unfold get_simulated_program.
                         apply labels_equiv_position_in. auto. constructor.
                    **** rewrite Heqp_str. apply labels_equiv_position_not_in.
                         auto. constructor.
                *** rewrite Heqp_str. apply labels_equiv_position_none.
    + unfold equiv_pos in H1.
      simpl. exists 0. replace (steps_str + 0) with steps_str.
      rewrite snap_str_eq. split.
      ++ apply H0.
      ++ apply H1.
      ++ lia.
Abort.

(* nth_error_skipn:
  forall [A : Type] (n : nat) (l : list A) (i : nat),
   nth_error (skipn n l) i = nth_error l (n + i) *)  


                  

              






(** ############## RASCUNHO ############# **)


(** x <- x + 1 *)

Check (incr_macro_1).

Definition get_state snap := 
  match snap with 
  | SNAP _ s => s
  end.

Definition get_position snap :=
  match snap with 
  | SNAP i _ => i
  end.



Definition macro_at (prog : StringLang.program) macro position :=
  exists t,
  skipn position prog = macro ++ t.


Definition tracked prog state macro macro_position m :=
  forall (i : nat) l_prog l_macro,
  i <= m -> 
  l_prog  = get_position (compute_program prog (SNAP macro_position state) i) ->
  l_macro = get_position (compute_program macro (SNAP 0 state) i) ->
  l_prog = l_macro + macro_position /\
  (i < m -> l_macro < length macro).


Lemma split_execution :
  forall prog state macro macro_position m,
  macro_at prog macro macro_position ->
  tracked prog state macro macro_position m ->
  forall i s_prog s_macro l_prog l_macro, i <= m ->
  (SNAP l_prog s_prog) = compute_program prog (SNAP macro_position state) i ->
  (SNAP l_macro s_macro) = compute_program macro (SNAP 0 state) i ->
  s_prog = s_macro /\ l_prog = l_macro + macro_position.
Proof.
  induction i; intros; destruct H.
  (* i = 0 *)
  - split; inversion H2; inversion H3; reflexivity.
  (* S i *) 
  - split.
    (*  s_prog = s_macro  *)
    + simpl in H2, H3.
      remember (compute_program prog (SNAP macro_position state) i) 
      as snap_prog.
      remember (compute_program macro (SNAP 0 state) i) as snap_macro.
      destruct snap_prog as [line_prog state_prog]. 
      destruct snap_macro as [line_macro state_macro].
      assert (state_prog = state_macro /\
              line_prog = line_macro + macro_position).
      { apply IHi; try (reflexivity). transitivity (S i); auto. }
      clear IHi. destruct H4. 
      assert (nth_error prog (line_macro + macro_position) =
              nth_error (skipn macro_position prog) line_macro).
      { rewrite nth_error_skipn, PeanoNat.Nat.add_comm; reflexivity. }
      assert (line_prog = line_macro + macro_position /\
      (i < m -> line_macro < length macro)).
      { unfold tracked in H0. apply H0.
        + transitivity (S i). 
          ++ apply PeanoNat.Nat.le_succ_diag_r.
          ++ apply H1.
        + rewrite <- Heqsnap_prog. reflexivity.
        + rewrite <- Heqsnap_macro. reflexivity. }
      destruct H7. rewrite H4 in H2.
      assert (line_macro < length macro).
      { apply H8, H1. }
      assert (nth_error (skipn macro_position prog) line_macro =
              nth_error macro line_macro).
      { rewrite H. apply nth_error_app1, H9. }
      unfold next_step in H2, H3. subst.
      rewrite H10 in H6. rewrite H6 in H2.
      ++ destruct (nth_error macro line_macro).
         +++ destruct i0. destruct s.
             ** injection H2; injection H3; intros; subst; reflexivity.
             ** injection H2; injection H3; intros; subst; reflexivity.
             ** destruct (ends_with (state_macro v) n);
           injection H2; injection H3; intros; subst; reflexivity.
         +++ injection H2; injection H3; intros; subst; reflexivity.
    (*  l_prog = l_macro + macro_position. *)
    + eapply H0.
      ++ rewrite <- H1; reflexivity.
      ++ rewrite <- H2; reflexivity.
      ++ rewrite <- H3; reflexivity.
Qed.

(** Mostrar que toda macro IF acompanha o programa geral *)
