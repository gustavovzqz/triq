From Stdlib Require Import Nat.
From Stdlib Require Import List.
From Stdlib Require Import ProofIrrelevance.
From Stdlib Require Import FunctionalExtensionality.

Import ListNotations.
Require Import Extraction.

Module SLang.

(** Elementos Básicos de um Programa *)

Inductive variable : Type :=
  | X : nat -> variable  (* input  *)
  | Z : nat -> variable  (* local  *)
  | Y : variable.        (* output *)

Inductive label : Type :=
  | A : nat -> label.

Inductive statement : Type :=
  | INCR : variable -> statement
  | DECR : variable -> statement
  | IF_GOTO   : variable -> option label -> statement
  | SKIP : variable -> statement.

Inductive instruction : Type :=
  | Instr : option label -> statement -> instruction.

Definition program := list instruction.

(** Decidibilidade e Auxiliares *)

Definition eqb_var v1 v2 := 
  match v1, v2 with 
  | X a, X b => a =? b
  | Z a, Z b => a =? b
  | Y, Y  => true
  | _, _ => false
  end.

Definition eqb_lbl l1 l2 :=
  match l1, l2 with 
  | A a, A b => a =? b
  end.

Theorem eqb_var_refl : forall v, eqb_var v v = true.
Proof.
  destruct v; try (apply PeanoNat.Nat.eqb_refl); reflexivity.
Qed.

Theorem var_eqb_eq : forall v1 v2 : variable, eqb_var v1 v2 = true <-> v1 = v2.
Proof.
  intros v1 v2. split; intros H.
  (* -> *) 
  destruct v1; destruct v2; (try discriminate).
  - simpl in H. rewrite PeanoNat.Nat.eqb_eq in H. rewrite H. reflexivity.
  - simpl in H. rewrite PeanoNat.Nat.eqb_eq in H. rewrite H. reflexivity.
  - reflexivity.
  (* <- *)
  - rewrite H. apply eqb_var_refl.
Qed.

Theorem var_eqb_neq : forall v1 v2 : variable, eqb_var v1 v2 = false <-> v1 <> v2.
Proof.
  intros v1 v2. split; intros H.
  - intros H1. rewrite H1 in H. rewrite eqb_var_refl in H. discriminate.
  - unfold not in H. destruct (eqb_var v1 v2) eqn:Heq.
    + apply var_eqb_eq in Heq. contradiction. 
    + reflexivity.
Qed.


Definition eq_inst_label (instr : instruction ) (opt_lbl : option label) :=
  match instr, opt_lbl with 
  | Instr (Some lbl_a) _, Some lbl_b => eqb_lbl lbl_a lbl_b
  | _, _                => false
  end.

(** Função para encontrar a posição da primeira instrução com certa label em um programa *)

Definition get_labeled_instr (p : program) (lbl : option label) :=
  let fix aux l n :=
    match l with 
    | h :: t => match (eq_inst_label h lbl) with 
                | true => n
                | false => aux t (n + 1)
                end
    | []     => n 
    end
  in aux p 0.



(** Notações. Adaptadas de: https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html *)

Declare Custom Entry com.
Declare Scope s_lang_scope.
Declare Custom Entry com_aux.

Notation "<{ e }>" := e (e custom com_aux) : s_lang_scope.
Notation "e" := e (in custom com_aux at level 0, e custom com) : s_lang_scope.
Notation "( x )" := x (in custom com, x at level 99) : s_lang_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : s_lang_scope.

Notation "x <- + 1" := (INCR x)
  (in custom com at level 50, left associativity).

Notation "x <- - 1" := (DECR x)
  (in custom com at level 50, left associativity).

Notation "x <- + 0" := (SKIP x)
  (in custom com at level 50, left associativity).


Notation "'IF' x 'GOTO' y " :=
         (IF_GOTO x y) 
           (in custom com at level 89, x at level 99,
            y at level 99) : s_lang_scope.

Notation "[ l ] s " := (Instr (l) s)
  (at level 0, s custom com at level 200) : s_lang_scope.

Notation "[ ] s " := (Instr None s)
  (at level 0, s custom com at level 200) : s_lang_scope.


Notation "'[ i1 ; .. ; iN ]'" := (cons i1 .. (cons iN nil) ..)
  (at level 0, i1 custom com, iN custom com) : s_lang_scope.

Open Scope s_lang_scope.

(* ===================================================================== *)


(** Estado de um Programa *)

Definition state := variable -> nat.

Definition empty : state := (fun _ => 0).

Definition t_update (m : state ) (x : variable) (v : nat) :=
  fun x' => if eqb_var x x' then v else m x'.

Definition t_incr (m : state ) (x : variable) :=
  let v := m x in 
  t_update m x (v + 1).

Definition t_decr (m : state ) (x : variable) :=
  let v := m x in 
  t_update m x (v - 1).

Inductive snapshot :=
  | SNAP : nat -> state -> snapshot.

Definition initial_snapshot := SNAP 0 empty.

Definition create_state x_list :=
 let fix aux nat_list s n := 
   match nat_list with 
   | h :: t => aux t (t_update s (X n) h) (n + 1)
   | []     =>  s
   end
 in aux x_list empty 0.


(** 
   steps_to programa s s' :=
   O programa de snapshot s possui como próxima snapshot s'
*)


Inductive steps_to : program -> snapshot -> snapshot -> Prop :=
  (* x <- x + 1 *)
  | S_Incr : forall program x i opt_lbl instruction st,
      nth_error program i = Some instruction ->
      instruction = ([opt_lbl] x <- + 1)     ->
      steps_to program (SNAP i st) (SNAP (i + 1) (t_incr st x))

  (* x <- x - 1 *)
  | S_Decr: forall program x i opt_lbl instruction st,
      nth_error program i = Some instruction ->
      (instruction = ([opt_lbl] x <- - 1))   ->
      steps_to program (SNAP i st) (SNAP (i + 1) (t_decr st x))

  (* x <- x + 0 *)
  | S_Skip: forall program x i opt_lbl instruction st,
      nth_error program i = Some instruction ->
      instruction = ([opt_lbl] x <- + 0 )    ->
      steps_to program (SNAP i st) (SNAP (i + 1) st)

  (* IF X != 0 GOTO l, x = 0 *)
  | S_If_0: forall program x i opt_lbl l instruction st,
      nth_error program i = Some instruction   ->
      st x = 0                                 ->
      (instruction = ([opt_lbl] IF x GOTO l )) ->
      steps_to program (SNAP i st) (SNAP (i + 1) st)

  (* IF X != 0 GOTO l, x != 0 *)
  | S_If_S: forall program x i j opt_lbl l instruction st,
      nth_error program i = Some instruction  ->
      st x <> 0                               ->
      instruction = ([opt_lbl] IF x GOTO l )  ->
      (get_labeled_instr program l = j) ->
      steps_to program (SNAP i st) (SNAP j st )

  (* 
     Não há instrução para a linha "i".
     Seja "n" o tamanho do programa, "i" um número natural e "j" o estado do programa e s = (i, j) a snapshot de um programa de tamanho n. O livro define que:

     1. O valor de "i" está restrito a: 1 <= i <= n + 1 
     2. Uma snapshot terminal é uma snapshot onde i = n + 1.

    Da forma como está implementado, qualquer snapshot que possua uma linha fora dos limites do programa possuirá como resultado ela mesma. 
*)

  | S_Out: forall program i st,
      nth_error program i = None ->
      steps_to program (SNAP i st) (SNAP i st).

Hint Constructors steps_to : stepdb.


(** Definição de uma função para obter o próximo passo usando o a propriedade steps_to como restrição *)


(* Primeira tentativa: sem usar refine *)

Definition next_step' (prog : program) (snap1 : snapshot) :
  {snap2 | steps_to prog snap1 snap2}.
Proof.
  destruct snap1. destruct (nth_error prog n) eqn:E.
  - destruct i. destruct s0.
    + exists (SNAP (n + 1) (t_incr s v)). eapply S_Incr.
      ++ exact E.
      ++ reflexivity.
    + exists (SNAP (n + 1) (t_decr s v)). eapply S_Decr.
      ++ exact E.
      ++ reflexivity.
    + destruct (s v) eqn:Hsv.
      ++ exists (SNAP (n + 1) s). eapply S_If_0; eauto.
      ++ remember (get_labeled_instr prog o0).
         exists (SNAP n1 s). eapply S_If_S; eauto.
         +++ intros H. rewrite H in Hsv. discriminate Hsv.
    + exists (SNAP (n + 1) s). eapply S_Skip; eauto.
   - exists (SNAP n s). apply S_Out. assumption.
Defined. 

(** Unicidade do passo *)

Theorem step_unique : forall p snap1 snap2 snap3,
  steps_to p snap1 snap2 ->
  steps_to p snap1 snap3 ->
  snap2 = snap3.
Proof.
  intros. destruct snap1. inversion H.
  + inversion H0; subst.
    ++ rewrite H4 in H10. inversion H10. reflexivity.
    ++ rewrite H4 in H10. inversion H10. 
    ++ rewrite H4 in H10. inversion H10. 
    ++ rewrite H4 in H9.  inversion H9. 
    ++ rewrite H4 in H9.  inversion H9. 
    ++ rewrite H4 in H11. inversion H11. 
  + inversion H0; subst.
    ++ rewrite H4 in H10. inversion H10. 
    ++ rewrite H4 in H10. inversion H10. reflexivity.
    ++ rewrite H4 in H10. inversion H10. 
    ++ rewrite H4 in H9.  inversion H9. 
    ++ rewrite H4 in H9.  inversion H9. 
    ++ rewrite H4 in H11. inversion H11. 
  + inversion H0; subst.
    ++ rewrite H4 in H10. inversion H10. 
    ++ rewrite H4 in H10. inversion H10. 
    ++ rewrite H4 in H10. inversion H10. reflexivity.
    ++ rewrite H4 in H9.  inversion H9. 
    ++ rewrite H4 in H9.  inversion H9. 
    ++ rewrite H4 in H11. inversion H11. 
  + inversion H0; subst.
    ++ rewrite H3 in H11. inversion H11. 
    ++ rewrite H3 in H11. inversion H11. 
    ++ rewrite H3 in H11. inversion H11. 
    ++ rewrite H3 in H10. inversion H10. reflexivity.
    ++ rewrite H3 in H10. inversion H10. subst. apply H11 in H5. destruct H5.
    ++ rewrite H3 in H12. inversion H12.
  + inversion H0; subst.
    ++ rewrite H3 in H12. inversion H12. 
    ++ rewrite H3 in H12. inversion H12. 
    ++ rewrite H3 in H12. inversion H12. 
    ++ rewrite H3 in H11. inversion H11. subst. apply H4 in H13. destruct H13.
    ++ rewrite H3 in H11. inversion H11. reflexivity.
    ++ rewrite H3 in H13. inversion H13. 
  + inversion H0; subst.
    ++ rewrite H5 in H9. inversion H9. 
    ++ rewrite H5 in H9. inversion H9. 
    ++ rewrite H5 in H9. inversion H9. 
    ++ rewrite H5 in H8. inversion H8. 
    ++ rewrite H5 in H8. inversion H8. 
    ++ reflexivity.
Qed.


(** Equivalência entre o passo e a função *)

Theorem next_step_equivalence' :
  forall p snap1 (H : {snap2 | steps_to p snap1 snap2}) ,
    (next_step' p snap1) = H <-> steps_to p snap1 (proj1_sig H).
Proof.
  intros p snap1 [snap2 proof]. split.
  (* Ida ==> *)
  + intros H. simpl. assumption.
  (* Volta <== *)
  + simpl. intros H. destruct (next_step' p snap1) as [snap2' proof']. 
    assert (snap2' = snap2). {eapply step_unique; eassumption. }
    subst. assert (proof = proof') by apply proof_irrelevance.
    subst. reflexivity.
Qed.


Theorem next_step_equivalence'':
  forall p snap1 snap2,
  (proj1_sig (next_step' p snap1)) = snap2 <-> steps_to p snap1 snap2.
Proof.
  intros. split.
  + intros H. remember (next_step' p snap1). destruct s as [snap' proof].
    simpl in H. rewrite <- H. assumption.
  + intros H. remember (next_step' p snap1). destruct s as [snap' proof].
    simpl. eapply step_unique; eassumption.
Qed.


(* Definição simples e equivalência tradicional. ! *)

Definition next_step (prog : program) (snap : snapshot) : snapshot :=
  match snap with
  | SNAP n s =>
    match nth_error prog n with
    | Some ([l] x <- + 1) => SNAP (n + 1) (t_incr s x)
    | Some ([l] x <- - 1) => SNAP (n + 1) (t_decr s x)
    | Some ([l] x <- + 0) => SNAP (n + 1) s
    | Some ([l] IF x GOTO j) =>
        match s x with
        | S m => SNAP (get_labeled_instr prog j) s
        | 0   => SNAP (n + 1) s
        end
    | None => SNAP n s
    end
  end.

Theorem next_step_equivalence:
  forall p snap1 snap2,
  (next_step p snap1) = snap2 <-> steps_to p snap1 snap2.
Proof.
  intros. split.
  - intros. destruct snap1. simpl in H. destruct (nth_error p n) eqn:E.
    + destruct i. destruct s0; subst; try (econstructor); (try reflexivity);
      try(eassumption).
     ++ destruct (s v) eqn:E2.
        +++ eapply S_If_0; try (eassumption); reflexivity.
        +++ eapply S_If_S; try (eassumption); try (reflexivity).
            * intros H. rewrite E2 in H. discriminate H.
    + subst. apply S_Out. assumption.
  - intros H. unfold next_step. inversion H; subst; rewrite H0;
    try(reflexivity).
     ++ rewrite H1; reflexivity.
     ++ destruct (st x).
        +++ exfalso. apply H1. reflexivity.
        +++ reflexivity.
Qed.

Fixpoint compute_program (p : program) snap n :=
  match n with
  | S n' => compute_program p ((next_step p snap )) n'
  | O    => snap
  end.


Definition HALT (s : state) (p : program) (n : nat) :=
  let inital_snap := SNAP 0 s in 
  let nth_snap := compute_program p inital_snap n in 

  match nth_snap with 
  | SNAP n' _ => n' = (length p) 
  end.

Definition PRG := 
  <{[ [] Y <- + 1
    ]}>.


Theorem prg_halts : exists (t : nat) (s : state),
  HALT s PRG t.
Proof.
  exists 1. exists empty. unfold HALT. simpl. reflexivity.
Qed.


Theorem prg_halts' : forall (s : state), exists t,
  HALT s PRG t.
Proof.
  intros s.  exists 1. unfold HALT. unfold compute_program. unfold PRG. reflexivity.
Qed.


(* Função definida pelo programa *)

Definition phi (p : program) (l : list nat) (n : nat)
  (halts : (HALT (create_state l) p n)) :=
  match (compute_program p (SNAP 0 (create_state l)) n) with
  | SNAP _ s => s Y
  end.


(* Programa Exemplo: Função Identidade *)
Definition id_prg := 

  let x := X 0 in
  let z := Z 0 in
  let y := Y in

  let a := Some (A 0) in 
  let b := Some (A 1) in 
  let e := Some (A 10) in 

  <{[[a] IF x GOTO b;
     [ ] z <- + 1;
     [ ] IF z GOTO e;
     [b] x <- - 1;
     [ ] y <- + 1;
     [ ] z <- + 1;
     [ ] IF z GOTO a]
    }>.


(* O programa para com o número 8 como entrada *)
Theorem id_prg_halts : exists (n : nat), HALT (create_state [8]) id_prg n.
Proof.
  intros. exists 43.
  cbv (* usar o reflexivity antes pode causar problemas *).  reflexivity. 
Qed.

(* Agora, o que eu quero provar é que o programa id_prg para, qualquer que seja o valor de x inicial. Porém, é mais fácil provar que o programa para para quaisquer valores de x y z no estado inicial. (poderia provara para todo estado inicial, mas achei mais complicado) *)

(* O programa para para quaisquer que sejam os valores iniciais de x0, y0 e z0 *)

Theorem id_prg_halts' : forall (x0 : nat) (y0 : nat) (z0 : nat),
  exists (t : nat), HALT
  (t_update (t_update (t_update empty (X 0) x0) (Z 0) z0) Y y0) id_prg t.
Proof.
  intros x0. unfold HALT. induction x0 as [| m]; intros.
  - exists 3. destruct z0; destruct y0; reflexivity.
  - destruct IHm with (y0 + 1) (z0 + 1). exists (5 + x). 
    simpl compute_program. 
   assert ((t_update (t_update (t_update empty (X 0) m) (Z 0) (z0 + 1)) Y
              (y0 + 1)) = ((t_incr (t_incr (t_decr (t_update 
              (t_update (t_update empty (X 0) (S m)) (Z 0) z0) Y y0) (X 0)) Y)
              (Z 0)))).
      { apply functional_extensionality. intros x0. unfold t_incr. 
        unfold t_decr. unfold t_update. rewrite eqb_var_refl. simpl.
        destruct x0; try (reflexivity); destruct n; try (reflexivity).
        + rewrite PeanoNat.Nat.sub_0_r. reflexivity. }
      rewrite <- H0. destruct z0; assumption.
Qed.

Theorem id_prg_halts'' : forall (x0 : nat),
  exists (t : nat), HALT (create_state [x0])
   id_prg t.
Proof.
  intros x0. unfold create_state. 
  assert ((t_update empty (X 0) x0) = 
  (t_update (t_update (t_update empty (X 0) x0) (Z 0) 0) Y 0)). 
  { apply functional_extensionality. intros x. unfold t_update. unfold empty.
    destruct (eqb_var (X 0) x) eqn:E;
    destruct (eqb_var Y x) eqn:E2; 
    destruct (eqb_var (Z 0) x) eqn:E3; try(reflexivity).
    + rewrite var_eqb_eq in E. rewrite var_eqb_eq in E2.
      subst. discriminate E2.
    + rewrite var_eqb_eq in E2. rewrite var_eqb_eq in E. subst. discriminate E2.
    + rewrite var_eqb_eq in E3. rewrite var_eqb_eq in E. subst. discriminate E3.
   }
  rewrite H. apply id_prg_halts'.
Qed.
 

Theorem id_prg_halts_1000 : exists (t : nat), HALT (create_state [1000])
  id_prg t.
Proof.
  apply id_prg_halts''.
Qed.

