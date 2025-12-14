(** * Prova de Equivalência do programa dos naturais para o programa de alfabeto com apenas um dígito *)

(** O objetivo deste arquivo é provar a equivalência entre o programa dos naturais
    para o programa de strings, no caso especial em que este possui apenas um
    símbolo. Veremos que, apesar de parecer muito simples, já que existe uma
    associação direta das instruções nos naturais para as em strings, diversos
    detalhes de implementação dificultam o progresso da prova. *)

From Triq Require NatLang.
From Triq Require NatLangProperties.
From Triq Require StringLang.
From Triq Require StringLangProperties.
From Triq Require Import LanguagesCommon.
From Triq Require Import LanguagesUtils.
From Coq Require Import Nat.
From Coq Require Import List.
From Coq Require Extraction.
From Coq Require Import Lia.
Import ListNotations.


(** * Definições Básicas para a Equivalência *)

(** Para não lidar com a complexidade do caso genérico, as definições foram adaptadas
    para contemplar as especificidades do caso de string 0. As macros possuem apenas
    uma instrução e as definições de equivalência podem ser simplificadas *)

Definition incr_string0 (s : StringLang.string) :=
  0 :: s.

Definition get_incr_macro_0 opt_lbl x :=
  StringLang.Instr opt_lbl (StringLang.APPEND 0 x).

Definition get_decr_macro_0 opt_lbl x : (StringLang.instruction) :=
  StringLang.Instr opt_lbl (StringLang.DEL x).

Definition get_if_macro_0 opt_lbl x l :=
StringLang.Instr opt_lbl (StringLang.IF_ENDS_GOTO x 0 l).

Definition get_str_macro0 (i_nat : NatLang.instruction) :
  (StringLang.instruction ) := 
  match i_nat with 
  | NatLang.Instr opt_lbl (NatLang.INCR x) => get_incr_macro_0 opt_lbl x
  | NatLang.Instr opt_lbl (NatLang.DECR x) =>  get_decr_macro_0 opt_lbl x
  | NatLang.Instr opt_lbl (NatLang.IF_GOTO x l) => get_if_macro_0 opt_lbl x l
end.

Fixpoint get_str_prg (nat_prg : NatLang.program) 
                          : StringLang.program  :=
  match nat_prg with
  | [] => []
  | i_nat :: rest =>
      (get_str_macro0 i_nat) :: (get_str_prg rest)
  end.



(** * Noções Principais de Equivalência *)

(** A ideia da prova consiste em acompanhar cada passo de cada programa. Como o passo
    em p_nat sempre acompanha o passo em p_str, as instruções e as macros sempre estarão
    lado a lado. A ideia de equivalência em posição é _suficiente_ para obter a instrução
    equivalente em p_str. *)



(* Para o caso genérico, ou de 2 digitos, preciso contar 
   a macro para conseguir obter a posição da instrução *)


Fixpoint get_equiv_simulated_position p_nat n :=
  match n with
  | S n' => match p_nat with 
            | h :: t => length [get_str_macro0 h]
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
  (* n' = get_equiv_simulated_position p_nat n *)
  n = n'.


(** Para obter o programa simulado, basta executar a função de obter a macro equivalente
    para cada instrução em p_nat. Observe que as labels são as mesmas dos dois lados. *)

Fixpoint get_simulated_program p_nat :=
  match p_nat with
  | h :: t => [get_str_macro0 h] ++ get_simulated_program t
  | [] => []
  end.

(** A conversão pode ser simplificada já que incrementar no programa de string0 
    é o mesmo que adicionar um elemento ao final. *)

Fixpoint nat_to_string0 n := 
  match n with
  | 0 => []
  | S n' => incr_string0 (nat_to_string0 n')
  end.

(** A propriedade que queremos mostrar que se mantém para cada passo de computação são as
    seguintes:
     - Os estados são equivalentes;
     - As posições são equivalentes.

   De tal forma que, para qualquer passo de computação em p_nat, o mesmo passo em p_str
   resultará em uma posição equivalente (exatamente a mesma linha) e em um estado 
   equivalente ao dos naturais *)

Definition state_equiv (s_nat : NatLang.state) (s_str : StringLang.state ) :=
  (* Se s_nat x = v, então string_to_nat (s_str x) também retorna v *)
  forall (x : variable) (v : StringLang.string ),
  nat_to_string0 (s_nat x) = v -> s_str x = v.

Definition snap_equiv
  (p_nat    : NatLang.program)
  (snap_nat : NatLang.snapshot)
  (p_str    : StringLang.program ) 
  (snap_str : StringLang.snapshot ) :=

  match snap_nat with
  | NatLang.SNAP n state_nat => (
      match snap_str with
      | StringLang.SNAP n' state_str =>
      state_equiv state_nat state_str  /\ equiv_pos p_nat n p_str n'
      end)
  end.

(** Para obter o estado equivalente, basta acoplar uma função de conversão ao resultado
    do estado original *)

Definition get_equiv_state nat_state : (StringLang.state ) :=
  (fun x => nat_to_string0 (nat_state x)).

(** É fácil mostrar que o resultado da função acima é, de fato, um estado equivalente
    pela definição anterior *)

Lemma get_equiv_state_correct : forall state_nat,
  state_equiv state_nat (get_equiv_state state_nat).
Proof.
  intros state_nat. unfold get_equiv_state. unfold state_equiv.
  intros x v state_x_eq_v. destruct (state_nat x) eqn:E.
  + simpl. rewrite <- state_x_eq_v. reflexivity.
  + rewrite <- state_x_eq_v. reflexivity.
Qed.



(** Em algum momento da prova, obteremos a k-ésima instrução em p_nat. Fato é que a 
    k-ésima instrução de p_str será a macro da instrução em p_nat. Pela estrutura do
    programa, dado que estamos consultando a mesma posição, a instrução em p_str
    é, obrigatoriamente, a macro da instrução em p_nat. *)


Lemma nat_nth_implies_string : forall p_nat n i, 
  nth_error p_nat n = Some i ->
  nth_error (get_simulated_program p_nat) n = Some (get_str_macro0 i).
Proof.
  induction p_nat as [|h t IH]; intros n i H; simpl in *.
  - rewrite nth_error_nil in H; inversion H.
  - destruct n.
    + simpl. inversion H. reflexivity.
    + simpl in H. simpl.
      apply IH. exact H.
Qed.


Lemma nat_nth_implies_string_none : forall p_nat n,
  nth_error p_nat n = None ->
  nth_error (get_simulated_program p_nat) n = None.
Proof.
  induction p_nat as [|h t IH]; intros n H; simpl in *.
  - rewrite nth_error_nil. reflexivity.
  - destruct n.
    + simpl in H. discriminate.
    + simpl. apply IH. exact H.
Qed.


Lemma eq_inst_label_nat_str : forall h l,
  NatLang.eq_inst_label h l = StringLang.eq_inst_label (get_str_macro0 h) l.
Proof.
  intros. destruct h. destruct s; reflexivity.
Qed.



Lemma label_equal_nat_str :
  forall p_nat p_str l,
    p_str = get_simulated_program p_nat ->
    NatLang.get_labeled_instr p_nat l
    = StringLang.get_labeled_instr p_str l.
Proof.
  induction p_nat as [|h t IH]; intros p_str l Hsim.
  - simpl. rewrite Hsim. simpl. reflexivity.
  - rewrite Hsim. simpl.
    unfold NatLang.get_labeled_instr, StringLang.get_labeled_instr.
    simpl. rewrite <- eq_inst_label_nat_str.
    destruct (NatLang.eq_inst_label h l) eqn:HL.
    + reflexivity.
    + simpl. remember (get_simulated_program t).
      pose proof (IH l0 l). pose proof (H eq_refl).
      simpl. unfold NatLang.get_labeled_instr in H0.
      unfold StringLang.get_labeled_instr in H0.
      f_equal. exact H0.
Qed.



(** * Executar uma Instrução e a Macro mantém as propriedades *)

(** ** x <- x + 1 *)

Lemma append_cons_equiv : forall n,
  nat_to_string0 n ++ [0] = 0 :: nat_to_string0 n.
Proof.
  induction n.
  + reflexivity.
  + simpl. unfold incr_string0. f_equal. apply IHn.
Qed.

Lemma incr_state_equiv: forall s s' v, 
  state_equiv s s' ->
  state_equiv (NatLang.incr s v) (StringLang.append 0 s' v).
Proof.
  intros. unfold state_equiv, NatLang.incr, StringLang.append, NatLang.update,
  StringLang.update. intros x v0. unfold state_equiv in H.
  destruct (eqb_var v x) eqn:E.
  + rewrite PeanoNat.Nat.add_comm. simpl. unfold incr_string0.
    intros.  rewrite <- H0. 
    assert (s' v = nat_to_string0 (s v)). {  apply H. reflexivity. }
    rewrite H1.  rewrite append_cons_equiv. reflexivity.
  + apply H.
Qed.

(** ** x <- x - 1 *)


Lemma decr_state_equiv: forall s s' v, 
  state_equiv s s' ->
  state_equiv (NatLang.decr s v) (StringLang.del s' v).
Proof.
  intros. unfold state_equiv, NatLang.decr, StringLang.del, NatLang.update,
  StringLang.update. intros x v0.
  destruct (eqb_var v x) eqn:E.
  - destruct (s v) eqn: sv.
    + unfold state_equiv in H. pose proof (H v []).
      rewrite sv in H0. pose proof (H0 eq_refl). simpl. intros Hempty.
      rewrite <- Hempty. rewrite H1. reflexivity.
    + unfold state_equiv in H. remember (nat_to_string0 (s v)).
      pose proof (H v l). rewrite Heql in H0. pose proof (H0 eq_refl).
      rewrite H1. rewrite sv. intros H2. simpl in H2. 
      rewrite PeanoNat.Nat.sub_0_r in H2. rewrite <- H2.
      reflexivity.
  - intros. unfold state_equiv in H. apply H, H0.
Qed.


(** ** if x != 0 goto l *)

Lemma ends_with_Sn_true: forall n, 
  (StringLang.ends_with (nat_to_string0 (S n)) 0) = true.
Proof.
  reflexivity.
Qed.


Lemma simulated_program_string_0 : forall p_nat,
  StringLang.program_over (get_simulated_program p_nat) 0.
Proof.
  induction p_nat.
  + reflexivity.
  + simpl. destruct a. destruct s; simpl; auto.
Qed.

Lemma equiv_state_string0 : forall s_nat,
  StringLang.state_over (get_equiv_state s_nat) 0.
Proof.
  unfold StringLang.state_over, StringLang.string_over, get_equiv_state.
  intros. induction (s_nat x).
  + apply I.
  + fold StringLang.string_over in *. simpl. split; auto.
Qed.


(** ** Um programa sobre n com estado sobre n nunca possui um caractere de 
       outra string e seu estado *)


Definition snap_over snap :=
  match snap with
  | StringLang.SNAP _ state => StringLang.state_over state
  end.

Lemma string_over_app_impl : forall h t n,
  StringLang.string_over (h ++ t) n ->
  StringLang.string_over h n /\ StringLang.string_over t n.
Proof.
  intros. induction h.
  - split.
    + apply I.
    + simpl in H. apply H.
  - split.
    + simpl. split.
      ++ destruct H; lia.
      ++ simpl in H. destruct H. pose proof (IHh H0). 
         apply H1.
    + simpl in H. destruct H. pose proof (IHh H0). 
      apply H1.
Qed.

Lemma string_over_app_impl' : forall h t n,
  StringLang.string_over h n /\ StringLang.string_over t n ->
  StringLang.string_over (h ++ t) n.
Proof.
  intros. induction h.
  + apply H.
  + simpl. simpl in H. destruct H. destruct H. split.
    ++ apply H.
    ++ apply IHh. auto.
Qed.

Lemma string_over_app : forall h t n,
StringLang.string_over h n /\ StringLang.string_over t n <->
StringLang.string_over (h ++ t) n. 
Proof.
  split.
  + apply string_over_app_impl'.
  + apply string_over_app_impl.
Qed.





  Lemma program_over_n_never_uses_Sn : forall n p_str initial_state,
  StringLang.program_over p_str n ->
  StringLang.state_over initial_state n ->
  forall step, snap_over (StringLang.compute_program p_str 
  (StringLang.SNAP 0 initial_state) step) n.
Proof.
  induction step.
  + auto.
  + simpl. unfold StringLang.next_step. 
    destruct (StringLang.compute_program p_str (StringLang.SNAP 0 initial_state) step).
    destruct (nth_error p_str n0) eqn:E.
    ++ destruct i, s0.
       +++ simpl. unfold StringLang.state_over. intros x.
           unfold StringLang.append. unfold StringLang.update.
           destruct (eqb_var).
           - simpl. apply string_over_app. split.
             * apply IHstep.
             * admit.
           - apply IHstep. 
       +++ simpl. unfold StringLang.state_over. Abort.


(** * Teorema principal *)

(**
    Queremos mostrar que, para qualquer passo nos naturais, existe uma sequência de
    passos no programa de strings em que o estado e as posições serão equivalentes.

    Como estamos no caso string0, podemos dizer de imediato que o n em strings é
    exatamente o mesmo do em nat. Assim, façamos indução em n.

  *CASO BASE* : n = 0, n' = n = 0.


   Como temos zero passos, basta mostrar que a noção de equivalência se aplica ao
   programa no estado inicial, ou seja, com a snap (s, 0) em nat e (s', 0) em string.

   Temos que 0 = 0, então são equivalentes em posição, e temos que s' foi obtido pela
   função de obter estados equivalentes (que já foi mostrada correta). Assim, vale para
   n = 0.

  *PASSO DA INDUÇÃO* : Suponha que vale para n, vamos mostrar que vale para S n.


   Seja (s, k) a snapshot do programa nos naturais após as execução dos n passos e 
   seja (s', k') a snapshot do programa de strings após n passos. Temos, pela HI, que
   s é equivalente à s' e k é igual à k'.

   Para mostrar que vale para (S n), precisamos executar um passo em cada programa e 
   mostrar que as propriedades se mantêm. 

   Seja instr a k-ésima instrução de k (a próxima a ser executada). Temos três casos

   - instr = x <- x + 1
   - instr = x <- x - 1
   - instr = IF X != 0 GOTO L

   Como o programa em strings simula o programa dos naturais, temos que a k-ésima
   instrução em p_str é justamente a macro da instrução em p_nat. Assim, basta
   executar a instrução em p_nat e em p_str e observar que tanto o estado como
   as posições são mantidas. Para os dois primeiros casos, basta mostrar a 
   equivalência das operações no estado e observar que teremos (k + 1) e (k + 1)
   como próxima instrução de cada programa (equivalentes). 

   Para o caso do IF. veja que, o estado sempre se mantém e a posição também, já
   que a posição da primeira instrução com a label em p_str é a mesma da nos nat.
   E se não pular para a label, os dois seguem em frente (k + 1) = (k + 1) *)

Theorem nat_implies_string :
  forall (p_nat : NatLang.program)
         (initial_state_nat : NatLang.state),

  exists (p_str : StringLang.program)
         (initial_state_str : StringLang.state),
 StringLang.program_over p_str 0 /\
 StringLang.state_over initial_state_str 0 /\

  forall (n : nat),
  exists (n' : nat),
  snap_equiv p_nat
             (NatLang.compute_program p_nat (NatLang.SNAP 0 initial_state_nat) n)
             p_str
             (StringLang.compute_program p_str (StringLang.SNAP 0 initial_state_str) n').
Proof.
  intros p_nat state_nat. exists (get_simulated_program p_nat). 
  exists (get_equiv_state state_nat). split.
  apply simulated_program_string_0. split.
  apply equiv_state_string0.
  intros n. exists n. 
  remember (get_simulated_program p_nat) as p_str.
  induction n.
  (* Caso base: n = 0 *)
  - split.
    + apply get_equiv_state_correct. 
    + destruct p_nat.
      ++ simpl. reflexivity.
      ++ simpl. reflexivity.
  (* Passo da indução *)
  - destruct (NatLang.compute_program p_nat (NatLang.SNAP 0 state_nat) n)
    as [k s] eqn:snap_nat. 
    destruct (StringLang.compute_program p_str (StringLang.SNAP 0 
    (get_equiv_state state_nat)) n) as [k' s'] eqn:snap_str. 
    destruct IHn. unfold equiv_pos in H0. rewrite <- H0 in *. clear H0.
    destruct (nth_error p_nat k) eqn:E. 
    + apply nat_nth_implies_string in E as E1.
      unfold snap_equiv. simpl. rewrite snap_nat.
         unfold NatLang.next_step. rewrite E. rewrite snap_str.
         unfold StringLang.next_step. rewrite <- Heqp_str in E1. 
         rewrite E1. simpl. destruct i as [opt_lbl statement].
         destruct statement; simpl.
         (* x <- x + 1 *)
      ++ split.
         * apply incr_state_equiv, H.
         * reflexivity.
         (* x <- x - 1 *)
      ++ split.
         * apply decr_state_equiv, H.
         * reflexivity.
        (* if x != 0 GOTO a *)
      ++ destruct (s v) eqn:sv.
         (* x = 0 *)
         * unfold state_equiv in H. assert ((s' v) = []). 
           { apply H. rewrite sv. reflexivity. }
           rewrite H0. simpl. split.
           ** unfold state_equiv. exact H.
           ** reflexivity.
        (* x != 0 *)
         * unfold state_equiv in H.
           remember (nat_to_string0 (s v)). pose proof (H v l).
           rewrite Heql in H0. pose proof (H0 eq_refl).
           rewrite H1, sv. rewrite ends_with_Sn_true. split.
           ** unfold state_equiv. exact H.
           ** unfold equiv_pos. apply label_equal_nat_str, Heqp_str.
    + apply nat_nth_implies_string_none in E as E1.
      simpl. rewrite snap_str. rewrite snap_nat. 
      unfold NatLang.next_step. unfold StringLang.next_step.
      rewrite E, Heqp_str, E1. simpl. split.
      ++ exact H.
      ++ reflexivity.
Qed.

Print Assumptions nat_implies_string.



