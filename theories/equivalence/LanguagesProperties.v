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



(** Propriedade: Ser simulado por

     O programa em p_nat é simulado pelo programa em p_str *)

Inductive simulated_by {k : nat} : NatLang.program -> StringLang.program k -> Prop :=
  | Simulated_Empty : (* O programa vazio simula o programa vazio *)
      simulated_by [] []

  | Simulated_Instr : (* As macros simulam as instruções correspondentes *)
      forall (i_nat : NatLang.instruction),
        simulated_by [i_nat] (get_str_macro k i_nat)
  | Simulated_App :  (* A concatenação de programas simulados também é um
                        programa simulado *)
      forall h_nat t_nat (h_str t_str : StringLang.program k),
        simulated_by h_nat h_str ->
        simulated_by t_nat t_str ->
        simulated_by (h_nat ++ t_nat) (h_str ++ t_str).



(** Propriedade: Equivalência de estados

   Um estado s_nat é equivalente a um estado s_string se, ao converter
   o resultado de (s_nat x) para strings, tamos o resultado de (s_str x).

   OBS: Eu tinha feito uma versão ingênua onde eu aplicava a conversão de
   strings para nat. O problema é que isso tornava necessário provar a
   corretude da aplicação sucessiva de conversões
*)

Definition state_equiv  (s_nat : NatLang.state) {k} (s_str : StringLang.state k) :=
  forall (x : variable) (v : StringLang.string k),
  (nat_to_string k (s_nat x)) = v -> s_str x = v.

(** Propriedade: Equivalência de Posição:
  
   O programa em p_nat na linha n é equivalente em posição ao programa
   p_str na linha n' se:
   1. Se a n-ésima linha de p_nat é vazia, então a n'-ésima linha
   de p_str também é vazia.
   2. Se a n-ésima linha de p_nat possui uma instrução h, então
   p_str possui a macro para esta instrução começando na linha n'.
*)

Definition equiv_pos 
  (p_nat : NatLang.program)
  (n : nat)
  {k : nat}
  (p_str : StringLang.program k)
  (n' : nat) :=
  match nth_error p_nat n with
  | None => nth_error p_str n' = None 
  | Some h => exists t, skipn n' p_str = get_str_macro k h ++ t 
  end.


(** Propriedade: Equivalência de Programa:
   TODO: Mudar nome e mudar texto. prog_snap equiv? ...  *)

Definition prog_equiv
  (p_nat    : NatLang.program)
  (snap_nat : NatLang.snapshot)
  {k : nat}
  (p_str    : StringLang.program k) 
  (snap_str : StringLang.snapshot k) :=

  match snap_nat with
  | NatLang.SNAP n state_nat => (
      match snap_str with
      | StringLang.SNAP n' state_str =>
      state_equiv state_nat state_str  /\ equiv_pos p_nat n p_str n'
      end)
  end.


(** Úteis *)

(* Obter um estado em string equivalente a um estado em nat *)
Definition get_equiv_state (k : nat) nat_state : (StringLang.state k) :=
  (fun x => nat_to_string k (nat_state x)).


(* A função de obter estado equivalente é correta 
   de acordo com a propriedade state_equiv *)
Lemma get_equiv_state_correct : forall state_nat k,
  state_equiv state_nat (get_equiv_state k state_nat).
Proof.
  intros state_nat k. unfold get_equiv_state. unfold state_equiv.
  intros x v state_x_eq_v. destruct (state_nat x) eqn:E.
  + simpl. rewrite <- state_x_eq_v. reflexivity.
  + rewrite <- state_x_eq_v. reflexivity.
Qed.

(* Se a concatenaçáo de duas listas não é vazia, então pelo menos uma delas
   não é vazia *)
Lemma app_not_nil : forall A (l1 : list A) l2, l1 ++ l2 <> [] ->
  l1 <> [] \/ l2 <> [].
Proof.
  intros A l1 l2 app. destruct l1; destruct l2.
  + simpl in app. exfalso. exact (app eq_refl).
  + right. intros H. discriminate H.
  + left. intros H. discriminate H.
  + right. intros H. discriminate H.
Qed.

(* Não é possível que um programa vazio seja simulado por um não vazio *)
Lemma simulated_empty_left_aux : forall p_nat {k} (p_str : StringLang.program k),
  (p_nat = []) ->
  (p_str <> []) ->
  simulated_by p_nat p_str -> False.  
Proof.
  intros p_nat k p_str p_nat_zero p_str_zero sim. induction sim.
  + exact (p_str_zero eq_refl).
  + discriminate p_nat_zero.
  + apply app_eq_nil in p_nat_zero. destruct p_nat_zero.
    apply app_not_nil in p_str_zero. destruct p_str_zero.
    ++ apply IHsim1; assumption.
    ++ apply IHsim2; assumption.
Qed.

(* Não é possível que um programa não vazio seja simulado por um vazio
   TODO: Falta definir get_str_macro .
*)
Lemma simulated_empty_right_aux : forall p_nat {k} (p_str : StringLang.program k),
  (p_nat <> []) ->
  (p_str = []) ->
  simulated_by p_nat p_str -> False.  
Proof.
  intros p_nat k p_str p_nat_zero p_str_zero sim. induction sim.
  + exact (p_nat_zero eq_refl).
  +  admit. (* TODO: Só consigo completar depois que get_str_macro estiver pronto *)
  + apply app_eq_nil in p_str_zero. destruct p_str_zero.
    apply app_not_nil in p_nat_zero. destruct p_nat_zero.
    ++ apply IHsim1; assumption.
    ++ apply IHsim2; assumption.
Admitted.

(* Os programs são equivalentes em posição na posição zero.
   OBS: Só copiei a prova que fiz para string 0 e completei o que faltava.

   Também existe uma versão mais forte desse teorema que precisará ser provada, 
   uma que diz:
   "Se estava em uma linha n e p_nat e em uma linha n' em p_nat, equivalentes
   em posição, a linha (n + 1) e (n' + k) também são equivalentes, onde k é o
   tamanho da macro da linha n'" *)

Lemma equiv_pos_simulated_0 : forall p_nat {k} (p_str : StringLang.program k),
  simulated_by p_nat p_str -> equiv_pos p_nat 0 p_str 0.
Proof.
  intros p_nat k p_str simulated_prf. unfold equiv_pos. 
  induction simulated_prf.
  + reflexivity.
  + simpl. exists []. rewrite app_nil_r. reflexivity.
  + destruct h_nat; destruct h_str; destruct t_nat; destruct t_str; try (assumption).
    ++ exfalso. apply simulated_empty_left_aux with [] k (i :: h_str).
       * reflexivity.
       * intros H. discriminate H.
       * assumption.
    ++ exfalso. apply simulated_empty_left_aux with [] k (i :: h_str).
       * reflexivity.
       * intros H. discriminate H.
       * assumption.
    ++ exfalso. apply simulated_empty_left_aux with [] k (i0 :: t_str).
       * reflexivity.
       * intros H. discriminate H.
       * assumption.
    ++ exfalso. apply simulated_empty_right_aux with (i :: h_nat) k [].
       * intros H. discriminate H.
       * reflexivity.
       * assumption.
    ++ rewrite app_nil_r. rewrite app_nil_r. assumption.
    ++ rewrite app_nil_r. simpl. simpl in IHsimulated_prf1.
       destruct IHsimulated_prf1. rewrite app_comm_cons. rewrite H.
       exists (x ++ i1 :: t_str). Search ((_ ++ _) ++ _ = _ ++ (_ ++ _)).
       rewrite app_assoc_reverse_deprecated. reflexivity.
    ++ rewrite app_nil_r.  assumption.
    ++ simpl. simpl in *. destruct IHsimulated_prf1.
       rewrite app_comm_cons. rewrite H. exists (x ++ i2 :: t_str).
       rewrite app_assoc_reverse_deprecated. reflexivity.
Qed.





(** Teorema principal *)
Theorem nat_implies_string :
  forall (p_nat : NatLang.program)
         (state_nat : NatLang.state)
         {k : nat}
         (p_str : StringLang.program k),
  simulated_by p_nat p_str ->

  exists (state_str : StringLang.state k), 

  forall (n : nat),
  exists (n' : nat),
  prog_equiv p_nat
             (NatLang.compute_program p_nat (NatLang.SNAP 0 state_nat) n)
             p_str
             (StringLang.compute_program p_str (StringLang.SNAP 0 state_str) n').
Proof.
  intros p_nat state_nat k p_str simulated_prf.
  exists (get_equiv_state k state_nat). induction n.
  - exists 0. split.
    + apply get_equiv_state_correct.
      (* tem um admit no equiv_pos_simulated_0, mas é trivial
         basta dizer que a macro nunca será vazia *)
    + apply equiv_pos_simulated_0, simulated_prf. 
 
