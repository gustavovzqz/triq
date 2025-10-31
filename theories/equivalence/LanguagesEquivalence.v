From Triq Require NatLang.
From Triq Require StringLang.
From Triq Require Import LanguagesCommon.
From Triq Require Import LanguagesUtils.
From Coq Require Import Nat.
From Coq Require Import List.
From Coq Require Extraction.
From Coq Require Import Lia.
Import ListNotations.

Search nat.


Lemma Sn_leq_n'_implies_n_leq_n' : forall n n', S n <= n' -> n <= n'.
Proof.
  lia.
Qed.


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

Extraction get_if_macro.

(* [] IF Y != 0 GOTO E *)

Compute get_if_macro 3 None Y None.

(* O programa é feio. Usar a definição indutiva de alfabeto
   torna o programa mais legível. Imagino que todo o resto ficará parecido,
   com a diferença que a prova seria obtida com inversion se eu
   precisasse ...
    1. Importa? Tem algum prejuízo?
*)

(* Seja PNat um programa nos naturais e n um natural.
   Seja S o estado de PNat após n passos.  *)


(* Equivalência de estados. 
  O estado de p_nat em n passos é equivalente ao estado de p_str em n' passos
   se:
   Para todo valor de x no estado de p_nat, ele possui o mesmo valor em p_str
   (em string...) *)

(* TODO: Provavelmente eu vou querer partir de algum estado anterior, sem ser
   o inicial. *)
Definition state_equiv {k : nat} n n' p_nat (p_string : StringLang.program k) :=
  let s_nat := NatLang.get_state p_nat n in 
  let s_string := StringLang.get_state p_string n'
  in
  forall x v, (s_nat x = v) -> (string_to_nat (s_string x) = v).

(* CBV é muito útil *)
Lemma state_equiv_0_0 : forall {k : nat} p_nat (p_str : StringLang.program k),
  state_equiv 0 0 p_nat p_str.
Proof.
  cbv. intros. assumption.
Qed.

Lemma nat_compute_program_empty : forall n snap,
  NatLang.compute_program [] snap n = snap.
Proof.
  induction n; intros.
  + reflexivity.
  + unfold NatLang.compute_program. assert (NatLang.next_step [] snap = snap).
    { unfold NatLang.next_step. destruct snap. rewrite nth_error_nil. reflexivity. }
    rewrite H. simpl. fold NatLang.compute_program. apply IHn.
Qed.

Lemma string_compute_program_empty :
  forall {k : nat} n (snap : StringLang.snapshot k),
  StringLang.compute_program [] snap n = snap.
Proof.
  induction n; intros.
  + reflexivity.
  + unfold StringLang.compute_program. assert (StringLang.next_step [] snap = snap).
    { unfold StringLang.next_step. destruct snap. rewrite nth_error_nil. reflexivity. }
    rewrite H. apply IHn.
Qed.




Lemma state_equiv_nil_nil: forall {k : nat} n n' p_nat (p_str : StringLang.program k),
  p_nat = []  ->
  p_str = [] ->
  state_equiv n n' p_nat p_str.
Proof.
  intros. subst. unfold state_equiv. intros.
  (* Reduzindo a expressão do goal *)
  unfold StringLang.get_state. 
  pose proof (string_compute_program_empty n'(StringLang.SNAP 0 (StringLang.empty k))).
  rewrite H0. cbv.
  (* Reduzindo a expressão Nat *)
  unfold NatLang.get_state in H. 
  pose proof (nat_compute_program_empty n NatLang.initial_snapshot).
  rewrite H1 in H. cbv in H. assumption.
Qed.




Theorem pablo0 : forall (p_nat : NatLang.program) (n : nat),
  exists (p_str : StringLang.program 0) (n' : nat),
  state_equiv n n' p_nat p_str.
Proof.
  intros. induction n. 
  + exists []. exists 0. apply state_equiv_0_0.
    (* Aqui eu tenho:
       Existe um n e um n' tal que p_nat e p_str são equivalentes.

       Preciso mostrar que existe um n'' que é equivalente ao p_nat usando 
       essa informação. *)
  + destruct IHn as [p_str]. destruct H as [n'].
    (* O programa p_str0 depende do programa p_nat. *)
    destruct p_nat as [|h t].
    (* p_nat = [] *)
    ++ exists []. exists 0. simpl. apply state_equiv_nil_nil; reflexivity.
    (* p_nat = h :: t *)
    ++ destruct h. destruct (NatLang.Instr o s). destruct s0 eqn:statement.
       * admit.
       * admit.
       * admit.
Abort.




