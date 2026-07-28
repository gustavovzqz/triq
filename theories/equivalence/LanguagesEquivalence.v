From Triq Require NatLang.
From Triq Require StringLang.

From Triq Require NatLangProperties.
From Triq Require StringLangProperties.

From Triq Require Import LanguagesCommon.
From Triq Require StringMacros.

From Triq Require NatUtils.
From Triq Require StringUtils.
From Triq Require LanguagesUtils.

From Stdlib Require Import Nat.
From Stdlib Require Import List.
From Stdlib Require Import Lia.

Import ListNotations.

(** Equivalência entre estados *)

Definition state_equiv (s_nat : NatLang.state) (s_str : StringLang.state) 
  (max_char : nat) :=
  forall (x : variable),
  LanguagesUtils.nat_to_string (s_nat x) max_char = s_str x.


Definition get_equiv_simulated_position 
  (p_nat : NatLang.program) 
  (n : nat)
  (max_char : nat) :=
fold_left
  (fun acc instr => acc + StringMacros.macro_length instr max_char)
  (firstn n p_nat)
0.

Definition equiv_pos 
  (p_nat : NatLang.program) (n : nat)
  (n' : nat) (max_char : nat) :=
  n' = get_equiv_simulated_position p_nat n max_char.


(** Obter Programa que Simula p_nat *)

Definition get_equiv_str_program p_nat max_char :=
  let max_label_nat := NatUtils.get_max_label p_nat in
  let max_z_nat := NatUtils.get_max_z p_nat in

  StringMacros.get_str_prg_rec p_nat max_char max_label_nat max_z_nat.


(** O programa que simula está limitado à max_char *)

Lemma equiv_str_program_over : forall p_nat max_char,
  StringLang.program_over (get_equiv_str_program p_nat max_char) max_char.
Proof.
  intros p_nat max_char.
  unfold get_equiv_str_program. 
  apply StringMacros.program_over_conversion.
Qed.

(** Obter Estado Convertido nat -> string *)

Definition get_equiv_str_state nat_state max_char : (StringLang.state ) :=
(fun x => LanguagesUtils.nat_to_string (nat_state x) max_char ).


(** incr_string_over *)

Lemma incr_string_over : forall s max_char,
StringLang.string_over s max_char ->
StringLang.string_over (LanguagesUtils.incr_string s max_char) max_char.
Proof.
  intros. induction s.
  + simpl. lia.
  + simpl in *. destruct H. destruct (a <? max_char) eqn:E.
    ++ simpl. split; auto. assert (a < max_char).
       rewrite PeanoNat.Nat.ltb_lt in E; auto. lia.
    ++ simpl. split; auto. lia.
Qed.

(** state_equiv_over *)

Lemma equiv_state_over : forall s_nat max_char,
StringLang.state_over (get_equiv_str_state s_nat max_char) max_char.
Proof.
  unfold StringLang.state_over. unfold get_equiv_str_state.
  intros. induction (s_nat x).
  + apply I.
  + apply incr_string_over, IHn.
Qed.


(* Lemma simulated_program_decomposition_if :
  forall p_nat i o x l max_char max_label_p_nat max_z_p_nat p_str,
  nth_error p_nat i = Some (NatLang.Instr o (NatLang.IF_GOTO x l)) ->
  p_str = StringMacros.get_str_prg_rec p_nat
  max_char max_label_p_nat max_z_p_nat ->

  exists t,
    p_str = (firstn (get_equiv_simulated_position p_nat i max_char) p_str)
    ++ (StringMacros.get_if_macro x o l max_char) ++ t.
Proof. 
Admitted.
 *)



(** Caso IF **)




Lemma fold_left_add_const :
forall l acc c max_char,
  fold_left
    (fun acc instr => acc + StringMacros.macro_length instr max_char)
    l (acc + c)
  =
  acc +
  fold_left
    (fun acc instr => acc + StringMacros.macro_length instr max_char)
    l c.
Proof.
  induction l as [|h t IH]; intros acc c max_char.
  - simpl. reflexivity.
  - simpl. pose proof (IH acc (c + StringMacros.macro_length h max_char)).
    replace (acc + (c + StringMacros.macro_length h max_char)) with 
      (acc + c + (StringMacros.macro_length h max_char))
    in H. rewrite H. reflexivity.
    lia.
Qed.

Lemma get_equiv_simulated_position_cons :
forall h t i max_char,
  get_equiv_simulated_position (h :: t) (S i) max_char =
  StringMacros.macro_length h max_char +
  get_equiv_simulated_position t i max_char.
Proof.
  intros.
  replace (h :: t) with ([h] ++ t).
  + unfold get_equiv_simulated_position. simpl.
    pose proof (fold_left_add_const (firstn i t) 
    (StringMacros.macro_length h max_char) 0 max_char).
    replace (StringMacros.macro_length h max_char + 0) 
    with (StringMacros.macro_length h max_char) in H by lia.
    exact H.
  + reflexivity.
Qed.

Lemma label_in_instr_cases: forall h t label,
  NatUtils.label_in_instr (h :: t) label = true ->
  NatUtils.label_in_instr [h] label = true \/
  (NatUtils.label_in_instr [h] label = false /\
   NatUtils.label_in_instr t label = true). 
Proof.
  intros h t label label_in_program.
  simpl in label_in_program. destruct h. simpl.
  destruct (eqb_opt_lbl o label) eqn:E; auto.
Qed.




(* Não quero que o get_str_macro simplifique. *)
Opaque StringMacros.get_str_macro. 

Lemma labels_equiv_position_in :
forall p_nat label_idx max_char max_lbl_nat max_z_nat,
  NatUtils.label_in_instr p_nat (Some (A label_idx)) = true ->
  max_lbl_nat >= label_idx ->
  let p_str := StringMacros.get_str_prg_rec p_nat max_char
               max_lbl_nat max_z_nat in
  equiv_pos
    p_nat
    (NatLang.get_labeled_instr p_nat (Some (A label_idx)))
    (StringLang.get_labeled_instr p_str (Some (A label_idx)))
    max_char.
Proof.
  induction p_nat as [|nat_line t];
  intros label_idx max_char max_lbl_nat max_z_nat;
  intros label_in_p_nat max_lbl_gt_label_idxl p_str; 

  remember (Some (A label_idx)) as label.
  (* p_nat = [] -> trivialmente falso já que não pode haver uma 
    label em um programa vazio *)
  - unfold NatUtils.label_in_instr in label_in_p_nat.
    discriminate.
  (* p_nat = nat_line ++ t, p_str = str_line ++ t' *)
  (* Temos que label_in_instr (nat_line ++ t) = true.
     Daí, temos dois casos para analisar
     1. label_in_instr nat_line = true (direto, estará em str_line)
     2. label_in_instr nat_line = false /\ label_in_instr t = true.
     Aqui usamos a hipótese de indução *)
  - simpl.
    (* Inspecionando a linha *)
    destruct nat_line as [opt_label instr] eqn:E.
    assert (NatUtils.label_in_instr [NatLang.Instr opt_label instr]
    label = true \/ 
    NatUtils.label_in_instr [NatLang.Instr opt_label instr] 
    label = false /\ NatUtils.label_in_instr t label = true) 
    as label_in_cases.
    { apply label_in_instr_cases; auto. } 
    destruct label_in_cases as [label_in_h | [label_in_h_false label_in_t]].
    (* Caso 1: label_in_instr nat_line = true *)
    + simpl. simpl in label_in_h.
      assert (eqb_opt_lbl opt_label label = true) as eq_label.
      { destruct (eqb_opt_lbl opt_label label); auto. }
      unfold p_str. simpl. rewrite eq_label. 
      assert (opt_label = label) as opt_eq.
      { destruct opt_label, label; try (discriminate); auto.
        simpl in eq_label. destruct l, l0. simpl in *.  
         f_equal. f_equal. rewrite <- PeanoNat.Nat.eqb_eq; auto. }
      rewrite opt_eq.
      rewrite StringMacros.get_labeled_instr_head. 
      unfold equiv_pos, get_equiv_simulated_position. reflexivity.
    (* Caso 2: label está na cauda *)
    + simpl in label_in_h_false.
      assert (NatLang.eq_inst_label (NatLang.Instr opt_label instr) label
      = false) as label_neq_opt_label.
      { unfold NatLang.eq_inst_label. simpl.
        destruct (eqb_opt_lbl opt_label label); auto. 
      }
      rewrite label_neq_opt_label. simpl. unfold equiv_pos. 
      rewrite get_equiv_simulated_position_cons.
      unfold p_str. simpl.
      assert (StringUtils.label_in_instr (StringMacros.get_str_macro 
      (NatLang.Instr opt_label instr) max_char max_lbl_nat max_z_nat
      (StringUtils.get_max_label (StringMacros.get_str_prg_rec 
      t max_char max_lbl_nat max_z_nat))) label = false ) 
      as label_not_in_h.
      { rewrite Heqlabel in *.
        simpl in label_neq_opt_label.
        apply StringMacros.nat_label_not_in_macro; auto.
        rewrite eqb_opt_lbl_symm. auto.
      }

      rewrite StringMacros.get_labeled_instr_app; auto.
      unfold StringMacros.macro_length.
      assert ((length (StringMacros.get_str_macro (NatLang.Instr opt_label 
      instr) max_char max_lbl_nat max_z_nat (StringUtils.get_max_label
        (StringMacros.get_str_prg_rec t max_char max_lbl_nat max_z_nat)
        ))) = length (StringMacros.get_str_macro 
        (NatLang.Instr opt_label instr) max_char 0 0 0)) as same_length.
      { apply StringMacros.macros_same_size. }

      apply f_equal2_plus; auto.
      unfold equiv_pos in *.
      rewrite Heqlabel in *.
      apply IHt; auto.
Qed.




(** Teorema Principal *)

Theorem nat_implies_string :
  forall (p_nat : NatLang.program)
         (initial_state_nat : NatLang.state)
         (max_char : nat),
  NatLangProperties.is_initial_state initial_state_nat ->

  exists (p_str : StringLang.program)
        (initial_state_str : StringLang.state),
  StringLang.program_over p_str max_char /\
  StringLang.state_over initial_state_str max_char /\

  forall (n : nat),
  exists (n' : nat),

  let (line_nat, state_nat) := NatLang.split_snap 
      (NatLang.compute_program p_nat (NatLang.SNAP 0 initial_state_nat) n)  in

  let (line_str , state_str) := StringLang.split_snap
            (StringLang.compute_program p_str (StringLang.SNAP 0 initial_state_str) n') in

  state_equiv state_nat state_str max_char /\
  equiv_pos p_nat line_nat line_str max_char /\
  state_str (Z (NatUtils.get_max_z p_nat + 1)) = [] /\
  state_str (Z (NatUtils.get_max_z p_nat + 2)) = [] /\
  StringLang.state_over state_str max_char.

Proof.
  (* intros *)
  intros p_nat initial_nat_state max_char initial_state_prop.
  (* exists simulated_program *)
  exists (get_equiv_str_program p_nat max_char).
  (* inital_str_state é o estado inicial de nat convertido *)
  exists (get_equiv_str_state initial_nat_state max_char).
  repeat split.
  (* o programa equivalente de strings possui apenas caracteres 
     dentro do limite max_char *)
  { apply equiv_str_program_over. }
  (* o estado de strings também está limitado à max_char *)
  { apply equiv_state_over. }
  (* ramo principal *)
  intros steps_nat.
  remember (get_equiv_str_program p_nat max_char) as p_str.
  remember (get_equiv_str_state initial_nat_state max_char) as initial_str_state.

  (* indução *)
  induction steps_nat as [| steps_nat IH].
  (* caso base *)
  - exists 0. split.
    + (* estados iniciais são equivalentes *) admit.
    + destruct initial_state_prop as [initial_y_zero initial_z_zero]. 
      rewrite Heqinitial_str_state.
      repeat split.
      ++ unfold get_equiv_str_state. rewrite initial_z_zero.
         reflexivity.
      ++ unfold get_equiv_str_state. rewrite initial_z_zero.
         reflexivity.
      ++ apply equiv_state_over.

  (* passo da indução *)
  - simpl.
    destruct (NatLang.compute_program p_nat 
    (NatLang.SNAP 0 initial_nat_state)
    steps_nat) as [pos_nat state_nat].
    destruct IH as [steps_str H_ind_str].

    (* trocando o objetivo por steps_str + x *)
    cut (exists n' : nat,
        let (line_nat, state_nat) :=
        NatLang.split_snap
        (NatLang.next_step p_nat (NatLang.SNAP pos_nat state_nat)) in
        let (line_str, state_str) := StringLang.split_snap
        (StringLang.compute_program p_str (
        (StringLang.compute_program p_str 
        (StringLang.SNAP 0 initial_str_state) steps_str)) n') in
        state_equiv state_nat state_str max_char /\
        equiv_pos p_nat line_nat line_str max_char /\
        state_str (Z (NatUtils.get_max_z p_nat + 1)) = [] /\
        state_str (Z (NatUtils.get_max_z p_nat + 2)) = [] /\
        StringLang.state_over state_str max_char).
    { intros [x cut_hip]. exists (x + steps_str).
      rewrite StringLangProperties.compute_program_add. auto. }

    simpl.
    (* snap em que cheguei após steps_str é pos_str state_str *)
    destruct (StringLang.compute_program p_str (StringLang.SNAP 0 
    initial_str_state) steps_str) as [pos_str state_str].

    (* qual a linha que está na posição pos_nat em p_nat
       para ser executada? *)
    destruct (nth_error p_nat pos_nat) eqn:p_nat_instr.
    (* caso 1: existe uma linha *)
    + (* qual a instrução dessa linha? *)
      destruct i, s.
      (* a. x <- x + 1 *)
      ++ admit.
      (* b. x <- x- - 1 *)
      ++ admit.
      (* c. IF v != 0 GOTO A *)
      ++ admit.
    (* caso 2: não existe uma linha na posição.
       neste caso, a execução do programa dos naturais não faz nada,
       basta também não fazer nada no programa de strings *)
    + simpl. exists 0. simpl. destruct H_ind_str;
      repeat (split; auto).
Admitted.
