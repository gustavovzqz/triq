From Triq Require StringLang.
From Triq Require NatLang.
From Triq Require Import LanguagesCommon.
From Triq Require Import LanguagesUtils.
From Triq Require StringUtils.
From Triq Require StringLangProperties.

From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

(* MACROS *)
(* ------------------------------------------------------------------ *)
(* IF MACRO *)

(*
  Em Nat
  [instr_lbl] IF X != 0 GOTO l 

  Em String max_char
  [instr_lbl] IF X ends 0 GOTO l
  ...
  [instr_lbl] IF x ends max_char GOTO l
*)

Fixpoint get_if_macro 
  (x : variable)
  (instr_lbl : option label)
  (goto_lbl : label)
  (max_char : nat) : StringLang.program :=

  match max_char with 
  | 0 => [StringLang.Instr instr_lbl (StringLang.IF_ENDS_GOTO x 0 goto_lbl)]
  | S n => 
           StringLang.Instr instr_lbl (StringLang.IF_ENDS_GOTO x max_char goto_lbl) ::
            (get_if_macro x instr_lbl goto_lbl n) 
  end.

Compute get_if_macro Y None (A 20) 10.

(* Auxiliares *)

(*  IF X ENDS Si GOTO Ai (1 <= i <= n) *)

Fixpoint get_if_macro_label
  (x : variable)
  (instr_lbl : option label)
  (max_char : nat) 
  (first_label : nat) : StringLang.program :=

  let goto_lbl := A (max_char + first_label) in 

  match max_char with 
  | 0 => [StringLang.Instr instr_lbl (StringLang.IF_ENDS_GOTO x 0 goto_lbl)]
  | S n => StringLang.Instr instr_lbl (StringLang.IF_ENDS_GOTO x max_char goto_lbl) :: 
           (get_if_macro_label x instr_lbl n first_label)
  end.

Compute get_if_macro_label Y None 10 3.

(* [Ai]  X <- X -
         Y <- S(i+1) Y ( 1 <= i < n)
         GOTO C  *)


Definition get_ai_block_incr 
  (x : variable)
  (z : variable)
  (aux : variable)
  (first_block_label : nat)
  (char : nat)
  (goto_label: label ) :=


let ai_label := Some (A (first_block_label + char))  in

[StringLang.Instr ai_label (StringLang.DEL x)] ++
[StringLang.Instr None (StringLang.APPEND (char + 1) z)] ++
[StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 goto_label)].


Fixpoint get_all_ai_blocks_incr 
  (x : variable)
  (z : variable)
  (aux : variable)
  (max_char : nat)
  (first_label : nat)
  (goto_label: label ) :=

match max_char with 
| 0 => get_ai_block_incr x z aux first_label 0 goto_label 
| S n => get_ai_block_incr x z aux first_label max_char goto_label  ++
         get_all_ai_blocks_incr x z aux n first_label goto_label
end.

Section test.

Let x := Z 0.
Let z := Z 1.
Let aux := Z 3.


Compute get_all_ai_blocks_incr x z aux 3 10 (A 30).
End test.

(*
  [Di]  X <- X -
        Y <- Si Y ( 1 <= i <= n )
        GOTO C
*)


Definition get_di_block 
  (x : variable)
  (z : variable)
  (aux : variable)
  (first_block_label : nat)
  (char : nat)
  (goto_label: label ) :=


let di_label := Some (A (first_block_label + char))  in

[StringLang.Instr di_label (StringLang.DEL x)] ++
[StringLang.Instr None (StringLang.APPEND char z)] ++
[StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 goto_label)].


Fixpoint get_all_di_blocks 
  (x : variable)
  (z : variable)
  (aux : variable)
  (max_char : nat)
  (first_label : nat)
  (goto_label: label ) :=

match max_char with 
| 0 => get_di_block x z aux first_label 0 goto_label 
| S n => get_di_block x z aux first_label max_char goto_label  ++
         get_all_di_blocks x z aux n first_label goto_label
end.

Section test.

Let x := Z 0.
Let z := Z 1.
Let aux := Z 3.


Compute get_all_di_blocks x z aux 5 0 (A 40).
End test.




Definition get_ai_block_decr 
  (x : variable)
  (z : variable)
  (aux : variable)
  (first_block_label : nat)
  (char : nat)
  (goto_label: label ) :=


let ai_label := Some (A (first_block_label + char))  in

[StringLang.Instr ai_label (StringLang.DEL x)] ++
[StringLang.Instr None (StringLang.APPEND (char - 1) z)] ++
[StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 goto_label)].


Fixpoint get_all_ai_blocks_decr
  (x : variable)
  (z : variable)
  (aux : variable)
  (max_char : nat)
  (first_label : nat)
  (goto_label: label ) :=

match max_char with 
| 0 => []
| 1 => get_ai_block_decr x z aux first_label 1 goto_label 
| S n => get_ai_block_decr x z aux first_label max_char goto_label  ++
         get_all_ai_blocks_decr x z aux n first_label goto_label
end.





(* INCR MACRO *)

(* [L] x <- x + 1 *)

(* 

  [L]   AUX <- a ++ AUX
  BLOCO 1

  [B]   IF X ENDS Si GOTO Ai (1 <= i <= n)
        Y <- S1 Y
        GOTO E
  

  BLOCO 2 
  [Ai]  X <- X -
        Y <- S(i+1) Y ( 1 <= i < n)
        GOTO C 

  BLOCO 3 
  [An]  X <- X -
        Y <- S1 Y 
        GOTO B 

  BLOCO 4 
  [C]   IF X ENDS Si GOTO Di (1 <= i <= n )
        GOTO E


  BLOCO 5
  [Di]  X <- X -
        Y <- Si Y ( 1 <= i <= n )
        GOTO C

  [E] AUX <- AUX -
*)


Definition get_incr_macro 
  (x : variable)
  (lbl : option label)
  (max_label_nat max_z_nat : nat)
  (max_label_str : nat)
  (max_char : nat) : StringLang.program :=


let z := Z (max_z_nat + 1) in 
let aux := Z (max_z_nat + 2 ) in

let B_idx  := max_label_nat + max_label_str + 1 in 
let A1_idx := B_idx  + 1 in
let An_idx := A1_idx + max_char in 
let C_idx  := An_idx + 1 in 
let D1_idx := C_idx + 1 in
let E_idx := D1_idx + max_char + 1 in


let B  := A B_idx  in
let A1 := A A1_idx in
let An := A An_idx in
let C  := A C_idx  in
let D1 := A D1_idx in
let E  := A E_idx  in

let goto l := 
  [StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 l)] in


(* aux <- a ++ [] *)
[StringLang.Instr lbl (StringLang.APPEND 0 aux)] ++ 

(* BLOCO 1 *) 
get_if_macro_label x (Some B) max_char A1_idx ++ 
[StringLang.Instr None (StringLang.APPEND 0 z)] ++ 
goto E ++

(* BLOCO 2 *) 

get_all_ai_blocks_incr x z aux (max_char - 1) A1_idx C ++

(* BLOCO 3 *)

[StringLang.Instr (Some An) (StringLang.DEL x)] ++
[StringLang.Instr None (StringLang.APPEND 0 z)] ++
[StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 C)] ++

(* BLOCO 4 *)
get_if_macro_label x (Some C) max_char D1_idx ++
goto E ++

(* BLOCO 5 *)

get_all_di_blocks x z aux max_char D1_idx C ++

(* ÚLTIMA LINHA 
   [E] aux <- - 
*)

[StringLang.Instr (Some E) (StringLang.DEL aux)].









(* DECR MACRO *)

(* 

  [L]   AUX <- a ++ AUX
  BLOCO 1

  [B]   IF X ENDS Si GOTO Ai (1 <= i <= n)
        GOTO E

  BLOCO 2 
  [Ai]  X <- X -
        Y <- S(i-1) Y ( 1 < i < n)
        GOTO C 

  BLOCO 3 
  [A1]  X <- X -
        IF X != 0 GOTO C2
        GOTO E 

  [C2] Y <- Sn Y
       GOTO B

  BLOCO 4 
  [C]   IF X ENDS Si GOTO Di (1 <= i <= n )
        GOTO E


  BLOCO 5
  [Di]  X <- X -
        Y <- Si Y ( 1 <= i <= n )
        GOTO C

  [E] AUX <- AUX -
*)

Definition get_decr_macro 
  (x : variable)
  (lbl : option label)
  (max_label_nat max_z_nat : nat)
  (max_label_str : nat)
  (max_char : nat) : StringLang.program :=

let z := Z (max_z_nat + 1) in 
let aux := Z (max_z_nat + 2 ) in

let B_idx  := max_label_nat + max_label_str + 1 in 
let A1_idx := B_idx  + 1 in
let An_idx := A1_idx + max_char in 
let C_idx  := An_idx + 1 in 
let C2_idx := C_idx + 1 in
let D1_idx := C2_idx + 1 in
let E_idx := D1_idx + max_char + 1 in


let B  := A B_idx  in
let A1 := A A1_idx in
let An := A An_idx in
let C  := A C_idx  in
let C2 := A C2_idx in
let D1 := A D1_idx in
let E  := A E_idx  in

let goto l := 
  [StringLang.Instr None (StringLang.IF_ENDS_GOTO aux 0 l)] in


(* aux <- a ++ [] *)
[StringLang.Instr lbl (StringLang.APPEND 0 aux)] ++ 

(* BLOCO 1 *) 
get_if_macro_label x (Some B) max_char A1_idx ++ 
goto E ++

(* BLOCO 2 *) 

get_all_ai_blocks_decr x z aux max_char A1_idx C ++

(* BLOCO 3 *)

[StringLang.Instr (Some A1) (StringLang.DEL x)] ++
get_if_macro x None C2 max_char ++
goto E ++

(* BLOCO 4 *)
get_if_macro_label x (Some C) max_char D1_idx ++
goto E ++

(* BLOCO 5 *)

get_all_di_blocks x z aux max_char D1_idx C ++

(* ÚLTIMA LINHA 
   [C] aux <- - 
*)

[StringLang.Instr (Some E) (StringLang.DEL aux)].










(* ------------------------------------------------------------------ *)

(* Str Macro and Programs *)

Definition get_str_macro 
  (i_nat : NatLang.instruction) 
  (max_char : nat) 
  (max_label_nat max_z_nat max_label_str : nat) 
  : (StringLang.program) := 
  match i_nat with 
  | NatLang.Instr o (NatLang.INCR x) => get_incr_macro x o max_label_nat
                                        max_z_nat max_label_str max_char
  | NatLang.Instr o (NatLang.DECR x) => get_decr_macro x o max_label_nat
                                        max_z_nat max_label_str max_char
  | NatLang.Instr o (NatLang.IF_GOTO x l) => get_if_macro x o l max_char
end.

(* Macro Length *)
(* Não tem problema chamar macro_length para uma macro com
   parâmetros para 0 0 0, já que todas as macros tem mesmo
   tamanho, fixando max_char. *)

Definition macro_length instr max_char :=
  length (get_str_macro instr max_char 0 0 0).


(* Getting the Str Program *)

Fixpoint get_str_prg_rec p_nat max_char max_label_p_nat max_z_p_nat :=
  match p_nat with
  | []     => []
  | h :: t => let str_rest := get_str_prg_rec t max_char 
              max_label_p_nat max_z_p_nat in 
              let max_label_rest := StringUtils.get_max_label str_rest in 
              (get_str_macro h max_char max_label_p_nat 
               max_z_p_nat max_label_rest)
               ++ str_rest
  end.



Lemma program_over_app : forall p p' max_char,
StringLang.program_over p  max_char  ->
StringLang.program_over p' max_char  ->
StringLang.program_over (p ++ p') max_char.
Proof.
  intros p p' max_char hp hp'; induction p.
  + simpl. apply hp'.
  + simpl. simpl in hp. destruct a. destruct s; auto.
    ++ destruct hp; auto.
    ++ destruct hp; auto.
Qed.

(* String Program is over max_char *)

(* IF *)

Lemma if_macro_over : forall x instr_lbl goto_lbl max_char,
  StringLang.program_over (get_if_macro x instr_lbl goto_lbl max_char) max_char.
Proof.
Admitted.

(* INCR *)

Lemma incr_macro_over : 
  forall x instr_lbl ml_nat mz_nat ml_str max_char,
  StringLang.program_over (get_incr_macro x instr_lbl ml_nat mz_nat ml_str max_char)
  max_char.
Proof.
Admitted.

(* DECR *)

Lemma decr_macro_over : 
  forall x instr_lbl ml_nat mz_nat ml_str max_char,
  StringLang.program_over (get_decr_macro x instr_lbl ml_nat mz_nat ml_str max_char)
  max_char.
Proof.
Admitted.


Lemma program_over_conversion : forall p_nat max_char max_label_nat max_z_nat , 
  StringLang.program_over 
  (get_str_prg_rec p_nat max_char max_label_nat max_z_nat ) max_char.
Proof.
  intros. induction p_nat.
  - apply I.
  - destruct a. destruct s; apply program_over_app; auto.
    + apply incr_macro_over.
    + apply decr_macro_over.
    + apply if_macro_over.
Qed.


Lemma macros_same_size : forall instr max_char max_lbl_nat max_z_nat 
      max_z_str,
  length (StringMacros.get_str_macro instr max_char max_lbl_nat max_z_nat
          max_z_str) =
  length (StringMacros.get_str_macro instr max_char 
          0 0 0).
Proof.
Admitted.

(** Simulated Program Decomposition *)

(* 
   NatLang.Instr o (NatLang.IF_GOTO x l) => get_if_macro x o l max_char *)

Lemma get_labeled_instr_app :
  forall l1 l2 lbl,
  StringUtils.label_in_instr l1 lbl = false ->
  StringLang.get_labeled_instr (l1 ++ l2) lbl
  =
  length l1 + StringLang.get_labeled_instr l2 lbl.
Proof.
  induction l1; intros.
  - simpl. reflexivity.
  - simpl. simpl in H. destruct a eqn:E1. simpl.
    destruct o.
    + simpl. rewrite eqb_lbl_symm.
      destruct (eqb_lbl lbl l).
      ++ discriminate H. 
      ++ f_equal. auto.
    + simpl. f_equal; auto.
Qed.




Lemma nat_label_not_in_macro : forall instr opt_label 
  max_char label_idx max_label_nat max_z_nat max_z_str,

  eqb_opt_lbl (Some (A label_idx)) opt_label = false ->
  max_label_nat >= label_idx ->


  StringUtils.label_in_instr
  (StringMacros.get_str_macro (NatLang.Instr opt_label instr) max_char
  max_label_nat max_z_nat max_z_str) (A label_idx) = false.
Proof.
  intros. destruct instr.
  + simpl.
  (* Essa prova não é conceitualmente difícil, mas é bem trabalhosa.
   *)
Admitted.




Lemma get_labeled_instr_head: forall label instr max_char
  max_label_nat max_z_nat max_z_str t,
  (StringLang.get_labeled_instr ( 
    (StringMacros.get_str_macro (NatLang.Instr (Some label) instr) max_char
    max_label_nat max_z_nat max_z_str) ++ t) label) = 0.
Proof.
  intros. simpl. destruct instr.
  - simpl. rewrite eqb_lbl_refl. reflexivity.
  - admit. (* depende da implementação de DECR *)
  - destruct max_char;
    simpl. rewrite eqb_lbl_refl; reflexivity.
Admitted.



(** Computando IF *)

Lemma compute_if_block_skip :
  forall max_char p_str pos_str state_str 
         instr_label x goto_label
         max_label_nat max_z_nat max_z_str h t, 

  p_str = h ++
  StringMacros.get_str_macro 
  (NatLang.Instr instr_label (NatLang.IF_GOTO x goto_label)) 
  max_char max_label_nat max_z_nat
  max_z_str ++ t  ->

  length h = pos_str  ->


  state_str x = [] ->

  exists n,
  let (line_str, state_str') :=
    StringLang.split_snap
      (StringLang.compute_program p_str (StringLang.SNAP pos_str state_str)
         n) in

  state_str' = state_str /\
  line_str = pos_str + StringMacros.macro_length 
  (NatLang.Instr instr_label (NatLang.IF_GOTO x goto_label)) 
  max_char.
Proof.
  Transparent StringMacros.get_str_macro.
  induction max_char;
  intros p_str pos_str state_str instr_label
  x goto_label max_label_nat max_z_nat max_z_str h t;
  intros p_str_decomposition H_length H_state_str.
  - rewrite p_str_decomposition. 
    exists 1. simpl. rewrite nth_error_app2; try lia.
    rewrite H_length, PeanoNat.Nat.sub_diag.
    simpl.
    rewrite H_state_str. simpl. unfold StringMacros.macro_length.
    repeat (split; auto).
    (* Passo *)
  - cut (exists n n' : nat, 
    let (line_str, state_str') := StringLang.split_snap
    (StringLang.compute_program p_str (StringLang.compute_program p_str 
    (StringLang.SNAP pos_str state_str) n) n') 
    in state_str' = state_str /\ line_str = pos_str + 
    StringMacros.macro_length 
    (NatLang.Instr instr_label (NatLang.IF_GOTO x goto_label)) (S max_char)).
    {intros cH. destruct cH as [m [m']]. exists (m' + m). 
     rewrite StringLangProperties.compute_program_add. auto. }
    exists 1. simpl. rewrite p_str_decomposition, nth_error_app2; try lia.
    rewrite <- p_str_decomposition.
    rewrite H_length, PeanoNat.Nat.sub_diag. simpl.
    rewrite H_state_str. simpl.
    simpl in p_str_decomposition.
    unfold StringMacros.macro_length in *. simpl. 
    remember  (length (StringMacros.get_if_macro x instr_label 
    goto_label max_char)) as if_length.
    replace (pos_str + S if_length) with (pos_str + 1 + if_length) by lia.
    rewrite Heqif_length. 
    rewrite LanguagesUtils.cons_app_assoc in p_str_decomposition.
    rewrite app_assoc in p_str_decomposition.
    remember  (h ++ [StringLang.Instr instr_label
    (StringLang.IF_ENDS_GOTO x (S max_char) goto_label)]) as h'.
    apply IHmax_char with (max_label_nat := max_label_nat)
    (max_z_nat := max_z_nat) (max_z_str := max_z_str)
    (h := h') (t := t); auto.
    rewrite Heqh', length_app, H_length. 
     reflexivity.
Qed.


Lemma compute_if_block_Sn :
  forall max_char p_str pos_str state_str 
         instr_label x goto_label
         max_label_nat max_z_nat max_z_str h t char,

  p_str = h ++
  StringMacros.get_str_macro 
  (NatLang.Instr instr_label (NatLang.IF_GOTO x goto_label)) 
  max_char max_label_nat max_z_nat
  max_z_str ++ t  ->

  length h = pos_str  ->

  char <= max_char ->

  StringLang.ends_with (state_str x) char = true ->

  exists n,
  let (line_str, state_str') :=
    StringLang.split_snap
      (StringLang.compute_program p_str (StringLang.SNAP pos_str state_str)
         n) in

  state_str' = state_str /\
  line_str = StringLang.get_labeled_instr p_str goto_label.
Proof.
  Transparent StringMacros.get_str_macro.
  induction max_char;
  intros p_str pos_str state_str instr_label
  x goto_label max_label_nat max_z_nat max_z_str h t char;
  intros p_str_decomposition H_length char_H H_state_str.
  - rewrite p_str_decomposition. 
    exists 1. simpl. rewrite nth_error_app2; try lia.
    rewrite H_length, PeanoNat.Nat.sub_diag.
    simpl. assert (char = 0) as char_0 by lia. rewrite char_0 in *.
    rewrite H_state_str. simpl. unfold StringMacros.macro_length.
    repeat (split; auto).
    (* Passo *)
  - cut (exists n n' : nat, 
    let (line_str, state_str') := StringLang.split_snap
    (StringLang.compute_program p_str (StringLang.compute_program p_str 
    (StringLang.SNAP pos_str state_str) n) n') 
    in state_str' = state_str /\ 
    line_str = StringLang.get_labeled_instr p_str goto_label).
    {intros cH. destruct cH as [m [m']]. exists (m' + m). 
     rewrite StringLangProperties.compute_program_add. auto. }
    exists 1. simpl. rewrite p_str_decomposition, nth_error_app2; try lia.
    rewrite <- p_str_decomposition.
    rewrite H_length, PeanoNat.Nat.sub_diag. simpl.
    assert (char = S max_char \/ char <> S max_char) as char_cases by lia.
    destruct char_cases as [char_eq_S | char_diff_S].
    + rewrite char_eq_S in *. rewrite H_state_str. simpl.
      simpl in p_str_decomposition.
      unfold StringMacros.macro_length in *. simpl.  exists 0.
      simpl. repeat split; auto.
    + assert (StringLang.ends_with (state_str x) (S max_char) = false) 
      as ends_with_S_false.
      { destruct (state_str x); auto. simpl in H_state_str. simpl. 
        rewrite PeanoNat.Nat.eqb_neq.
        rewrite PeanoNat.Nat.eqb_eq in H_state_str. lia. }
      assert (char <= max_char) as char_leq_max_char by lia.
      rewrite ends_with_S_false. simpl in p_str_decomposition.
      rewrite LanguagesUtils.cons_app_assoc in p_str_decomposition.
      rewrite app_assoc in p_str_decomposition.
      remember  (h ++ [StringLang.Instr instr_label
      (StringLang.IF_ENDS_GOTO x (S max_char) goto_label)]) as h'.
      apply IHmax_char with (max_label_nat := max_label_nat)
      (max_z_nat := max_z_nat) (max_z_str := max_z_str) 
      (instr_label := instr_label) (x := x) (char := char)
      (h := h') (t := t); auto.
      rewrite Heqh', length_app, H_length. reflexivity.
Qed.


