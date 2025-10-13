(** * Exemplos da Linguagem Baseada em Naturais *)

From Triq Require Import NatLang.

From Stdlib Require Import Nat.
From Stdlib Require Import List.
From Stdlib Require Import FunctionalExtensionality.
Import ListNotations.
Require Import Extraction.
Open Scope nat_lang_scope.


(** Programa Exemplo: Função Identidade *)

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


(**  O programa para com o número 8 como entrada *)
Theorem id_prg_halts : exists (n : nat), HALT (create_state 8) id_prg n.
Proof.
  intros. exists 43.
  cbv (* usar o reflexivity antes pode causar problemas *).  reflexivity.
Qed.

(** Agora, o que eu quero provar é que o programa id_prg para,
    qualquer que seja o valor de x inicial. Porém, é mais fácil
    provar que o programa para para quaisquer valores de x y z
    no estado inicial. (poderia provar para todo estado inicial,
    mas achei mais complicado) *)

(** O programa para para quaisquer que sejam 
    os valores iniciais de x0, y0 e z0 *)

Theorem id_prg_halts' : forall (x0 : nat) (y0 : nat) (z0 : nat),
  exists (t : nat), HALT
  (update (update (update empty (X 0) x0) (Z 0) z0) Y y0) id_prg t.
Proof.
  intros x0. unfold HALT. induction x0 as [| m]; intros.
  - exists 3. destruct z0; destruct y0; reflexivity.
  - destruct IHm with (y0 + 1) (z0 + 1). exists (5 + x). 
    simpl compute_program. 
   assert ((update (update (update empty (X 0) m) (Z 0) (z0 + 1)) Y
              (y0 + 1)) = ((incr (incr (decr (update 
              (update (update empty (X 0) (S m)) (Z 0) z0) Y y0) (X 0)) Y)
              (Z 0)))).
      { apply functional_extensionality. intros x0. unfold incr. 
        unfold decr. unfold update. rewrite eqb_var_refl. simpl.
        destruct x0; try (reflexivity); destruct n; try (reflexivity).
        + rewrite PeanoNat.Nat.sub_0_r. reflexivity. }
      rewrite <- H0. destruct z0; assumption.
Qed.

(** Agora posso escrever a versão original *)

Theorem id_prg_halts'' : forall (x0 : nat),
  exists (t : nat), HALT (create_state x0)
   id_prg t.
Proof.
  intros x0. unfold create_state. 
  assert ((update empty (X 0) x0) = 
  (update (update (update empty (X 0) x0) (Z 0) 0) Y 0)). 
  { apply functional_extensionality. intros x. unfold update. unfold empty.
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

Theorem id_prg_halts_1000 : exists (t : nat), HALT (create_state 1000)
  id_prg t.
Proof.
  apply id_prg_halts''.
Qed.


(** f(x) = 1 é Parcialmente Computável *)


Definition f (x : nat) := Some 1.


Definition prog := 
  <{[[] Y <- + 1]}>.



Theorem f_part_comp : partially_computable f.
Proof.
  unfold partially_computable. exists prog. intros x0. unfold f.
  split.
  + intros H. discriminate H.
  + intros H. exists 2. split.
    ++ unfold HALT. simpl. reflexivity.
    ++ unfold get_Y. simpl. reflexivity.
Qed.
