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


Require Import Setoid.

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
  destruct o; auto.
  destruct (eqb_lbl label l); auto.
Qed.



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


Lemma simulated_program_decomposition:
  forall p_nat p_str i instr max_char max_label_nat max_z_nat,
  nth_error p_nat i = Some instr ->
  p_str = StringMacros.get_str_prg_rec p_nat
  max_char max_label_nat max_z_nat ->

  exists t max_z_str,
    p_str = (firstn (get_equiv_simulated_position p_nat i max_char) p_str)
    ++ (StringMacros.get_str_macro instr max_char max_label_nat max_z_nat max_z_str)
    ++ t /\ length (firstn (get_equiv_simulated_position p_nat i max_char) p_str)
             = get_equiv_simulated_position p_nat i max_char.
Proof. 
  induction p_nat as [|h t]; 
  intros p_str i instr max_char max_label_nat max_z_nat;
  intros h_instr p_str_eq.
  - rewrite nth_error_nil in h_instr. discriminate.
  - destruct i.
    + simpl in h_instr. injection h_instr as h_eq. rewrite h_eq in *.
      simpl; eauto.
    + rewrite get_equiv_simulated_position_cons.
      simpl in p_str_eq.
      remember (StringUtils.get_max_label
      (StringMacros.get_str_prg_rec t max_char max_label_nat max_z_nat))
      as max_label_str. 
      remember (StringMacros.get_str_macro h max_char 
      max_label_nat max_z_nat max_label_str) as h'.
      remember (StringMacros.get_str_prg_rec t max_char max_label_nat 
      max_z_nat) as t' eqn:E.
      simpl in h_instr.
      assert (exists t0 max_z_str, 
      t' = firstn (get_equiv_simulated_position t i max_char) t' ++
      (StringMacros.get_str_macro instr max_char max_label_nat max_z_nat 
      max_z_str) ++ t0 /\
      length (firstn (get_equiv_simulated_position t i max_char) t') =
      get_equiv_simulated_position t i max_char) as t'_split.
      { eapply IHt; eauto. }
      destruct t'_split as [t''  [max_z_str [t'_eq t'_length]]].
      rewrite p_str_eq.
      assert ((StringMacros.macro_length h max_char) = (length h')) 
      as length_h'_eq.
      { unfold StringMacros.macro_length. rewrite Heqh'.
        symmetry. apply StringMacros.macros_same_size. }
      assert ((firstn (StringMacros.macro_length h max_char +
      get_equiv_simulated_position t i max_char) (h' ++ t'))
      = (h' ++ firstn (get_equiv_simulated_position t i max_char) t'))
      as firstn_split.
      { rewrite length_h'_eq. apply firstn_app_2. }
      exists t'', max_z_str. rewrite firstn_split. split.
      ++ rewrite t'_eq at 1. rewrite app_assoc. reflexivity.
      ++ rewrite length_app, t'_length, length_h'_eq.
         reflexivity.
Qed.





(* Não quero que o get_str_macro simplifique. *)
Opaque StringMacros.get_str_macro. 

Lemma labels_equiv_position_in :
forall p_nat label_idx max_char max_lbl_nat max_z_nat,
  NatUtils.label_in_instr p_nat (A label_idx) = true ->
  max_lbl_nat >= label_idx ->
  let p_str := StringMacros.get_str_prg_rec p_nat max_char
               max_lbl_nat max_z_nat in
  equiv_pos
    p_nat
    (NatLang.get_labeled_instr p_nat (A label_idx))
    (StringLang.get_labeled_instr p_str (A label_idx))
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
    (A label_idx) = true \/ 
    NatUtils.label_in_instr [NatLang.Instr opt_label instr] 
    (A label_idx) = false /\ NatUtils.label_in_instr t (A label_idx) = true) 
    as label_in_cases.
    { apply label_in_instr_cases; auto. } 
    destruct label_in_cases as [label_in_h | [label_in_h_false label_in_t]].
    (* Caso 1: label_in_instr nat_line = true *)
    + simpl. simpl in label_in_h. destruct opt_label; try discriminate.
      destruct l. simpl. rewrite PeanoNat.Nat.eqb_sym.
      assert (label_idx =? n = true) as label_idx_eq_n.
      { destruct (label_idx =? n); auto. }
      rewrite label_idx_eq_n. unfold equiv_pos, get_equiv_simulated_position.
      simpl. unfold p_str. simpl. rewrite PeanoNat.Nat.eqb_eq in label_idx_eq_n.
      rewrite label_idx_eq_n, StringMacros.get_labeled_instr_head.
      reflexivity.
    (* Caso 2: label está na cauda *)
    + unfold NatUtils.label_in_instr in label_in_h_false.
      simpl. assert ( eqb_opt_lbl opt_label (Some (A label_idx)) = false)
      as eqb_opt_false.
      { destruct opt_label; auto. simpl. 
        rewrite eqb_lbl_symm. destruct (eqb_lbl (A label_idx) l); auto. }
      rewrite eqb_opt_false.
      unfold p_str, equiv_pos. 
      rewrite get_equiv_simulated_position_cons.
      simpl. rewrite StringMacros.get_labeled_instr_app. 
      ++ unfold StringMacros.macro_length.
         rewrite StringMacros.macros_same_size.
         apply f_equal2_plus; auto.
         apply IHt; auto.
      ++ apply StringMacros.nat_label_not_in_macro; auto.
         rewrite eqb_opt_lbl_symm. auto.
Qed.


(** IF **) 

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

Lemma get_equiv_simulated_position_Sn :
  forall p_nat n instr max_char,
  nth_error p_nat n = Some instr ->
  get_equiv_simulated_position p_nat (n + 1) max_char
  = get_equiv_simulated_position p_nat n max_char + 
    StringMacros.macro_length instr max_char.
Proof.
  intros p_nat n instr max_char Hnth.
  unfold get_equiv_simulated_position.
  rewrite firstn_S_nth_error with (x := instr); auto.
  rewrite fold_left_app. simpl. lia.
Qed.

Lemma exists_split : forall P,
  (exists m m', P (m + m')) ->
  exists n', P n'.
Proof.
  intros. destruct H as [m' [m'' H]].
  exists (m' + m''); auto.
Qed.

Lemma cons_app_assoc: forall A (h : list A) a b ,
  h ++ (a :: b) = (h ++ [a] ++ b).
Proof.
  intros. simpl. reflexivity.
Qed.

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
    rewrite cons_app_assoc in p_str_decomposition.
    rewrite app_assoc in p_str_decomposition.
    remember  (h ++ [StringLang.Instr instr_label
    (StringLang.IF_ENDS_GOTO x (S max_char) goto_label)]) as h'.
    apply IHmax_char with (max_label_nat := max_label_nat)
    (max_z_nat := max_z_nat) (max_z_str := max_z_str)
    (h := h') (t := t); auto.
    rewrite Heqh', length_app, H_length. 
     reflexivity.
Qed.



Theorem if_macro_simulates :
  forall p_nat pos_nat state_nat
               pos_str state_str
         max_char x instr_label goto_label,

  let p_str := get_equiv_str_program p_nat max_char in


  nth_error p_nat pos_nat = Some (NatLang.Instr instr_label
  (NatLang.IF_GOTO x goto_label)) ->

  state_equiv state_nat state_str max_char ->

  equiv_pos p_nat pos_nat pos_str max_char ->

  exists n' : nat,
    let (line_nat, state_nat') :=
      NatLang.split_snap
        (NatLang.next_step p_nat (NatLang.SNAP pos_nat state_nat)) in
    let (line_str, state_str') :=
      StringLang.split_snap
        (StringLang.compute_program p_str (StringLang.SNAP pos_str state_str)
           n') in
    state_equiv state_nat' state_str' max_char /\
    equiv_pos p_nat line_nat line_str max_char /\
    state_str' = state_str.
Proof.
  intros p_nat pos_nat state_nat pos_str state_str
  max_char x instr_label goto_label p_str.
  intros nth_pos_nat_instr H_state_equiv H_equiv_pos. 
  unfold get_equiv_str_program in p_str.

  (* naming *)
  remember (NatLang.Instr instr_label (NatLang.IF_GOTO x goto_label)) 
  as if_instr eqn:if_instr_eq.
  remember (NatUtils.get_max_label p_nat) as max_label_nat.
  remember (NatUtils.get_max_z p_nat) as max_z_nat.

  (* str program decomposition *)
  assert (exists (t : list StringLang.instruction) (max_z_str : nat),
  p_str = firstn (get_equiv_simulated_position p_nat pos_nat max_char) 
  p_str ++ StringMacros.get_str_macro if_instr max_char max_label_nat 
  max_z_nat max_z_str ++ t /\
  length (firstn (get_equiv_simulated_position p_nat pos_nat max_char) p_str)
  = get_equiv_simulated_position p_nat pos_nat max_char)
  as [t [max_z_str [str_program_decomposition length_decomposition]]].
  { apply simulated_program_decomposition; auto. }

  simpl. rewrite nth_pos_nat_instr, if_instr_eq.
  destruct (state_nat x) eqn:state_nat_value.
  - unfold state_equiv in H_state_equiv. simpl in H_state_equiv.
    pose proof (H_state_equiv x) as state_str_value.
    rewrite state_nat_value in state_str_value. simpl in state_str_value.

    assert (exists n', let (line_str, state_str') :=
            StringLang.split_snap (StringLang.compute_program p_str 
            (StringLang.SNAP pos_str state_str) n') in
           state_str' = state_str /\
           line_str = pos_str + StringMacros.macro_length if_instr max_char)
    as [k if_computation].
    { rewrite if_instr_eq in *. apply compute_if_block_skip
      with (max_label_nat := max_label_nat) (max_z_nat := max_z_nat)
      (max_z_str := max_z_str) 
      (h := firstn (get_equiv_simulated_position p_nat pos_nat max_char) p_str)
      (t := t); auto.
      rewrite H_equiv_pos. auto. }
    exists k.
    destruct (StringLang.compute_program p_str 
    (StringLang.SNAP pos_str state_str) k). simpl in if_computation.
    destruct if_computation as [state_str_eq line_str_eq].
    simpl. rewrite state_str_eq, line_str_eq.
    repeat split.
    + auto.
    + unfold equiv_pos in *. rewrite H_equiv_pos.
      erewrite get_equiv_simulated_position_Sn; eauto.
  - admit.
Admitted.









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
