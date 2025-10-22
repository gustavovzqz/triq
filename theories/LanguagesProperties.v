From Triq Require NatLang.
From Triq Require StringLang.

From Coq Require Import Nat.
From Coq Require Import List.
From Coq Require Extraction.
Import ListNotations.

Search nat.

(** Conversão de String para Nat *)

(* Será que vou precisar usar? ... *)
Definition string_to_nat {n : nat} (s : StringLang.string n) :=
  let fix aux l k {struct l}:=
  match l with 
  | h :: t => ((proj1_sig h + 1) * (n ^ k)) + aux t (k - 1)
  | []  => 0
  end
   in aux s (length s - 1).



(** Conversão de Nat para String *)

Lemma lt_n_Sn : forall n m, n < m -> S n < S m.
Proof.
  intros n m le_nm. unfold lt. unfold lt in le_nm.
  apply le_n_S. exact le_nm.
Qed.

(* Resumo da Função de Incremento:

   1. Se o alfabeto for vazio, o resultado sempre será a string vazia.
   2. Trabalharemos com a lista invertida.
      [a, b, c, d] -> [d, c, b, a]
   3. Veja o elemento d. Se ainda puder ser incrementado, incremente-o. Se
   Estiver no limite, troque-o por zero e incremente c recursivamente.

   Exemplo: Alfabeto = 2, entrada = [1, 0, 1, 1]
   1. Alfabeto diferente de zero.
   2. Inverter lista: [1, 0, 1, 1] -> [1, 1, 0, 1]
   3. [0, 1, 0 1] -> [0, 0, 0, 1] -> [0, 0, 1, 1]
   4. Desinverter a lista: [0, 0, 1, 1] -> [1, 1, 0 0] *)


Definition incr_string {n : nat} (s : StringLang.string n) : (StringLang.string n). Proof.
  destruct n eqn:E.
  + exact [].
  + refine (let k := rev s in 
  let fix aux l :=
  match l with 
  | h :: t => ((match (proj1_sig h <? (n - 1) ) as eq return 
               ((proj1_sig h <? (n - 1) = eq)) -> _ with
              | true  => fun _ => ((exist _ ((proj1_sig h) + 1) _) :: t)
              | false => fun _ => (exist _ 0 _) :: (aux t)
              end) _)
  | [] =>  [exist _ 0 _]
  end 
  in rev (aux k)).
  ++ apply PeanoNat.Nat.lt_0_succ. 
  ++ rewrite PeanoNat.Nat.ltb_lt in e. rewrite E in e. 
     assert (S n0 - 1 = n0) by  apply PeanoNat.Nat.sub_0_r.
     rewrite  H in e. rewrite PeanoNat.Nat.add_1_r. apply lt_n_Sn, e.
  ++ apply PeanoNat.Nat.lt_0_succ.
  ++ reflexivity.
Defined.


(** Nat para String, basta usar o incremento n vezes *)

Fixpoint nat_to_string (k : nat) (n : nat) : (StringLang.string k)  :=
    match n with
    | S n' => incr_string (nat_to_string k n')
    | 0 => []
    end.


Fixpoint string_to_nat_list {n : nat} (s : StringLang.string n) :=
  match s with 
  | h :: t => (proj1_sig h) :: (string_to_nat_list t)
  | [] => []
  end.

Compute nat_to_string 2 5.

Definition nat_to_nat_list a b := (string_to_nat_list (nat_to_string a b)).



Definition a: (StringLang.alphabet 3).
Proof.
  exists 0; repeat (constructor).
Defined.

Definition b: (StringLang.alphabet 3).
Proof. 
  exists 1; repeat (constructor).
Defined.

Definition c: (StringLang.alphabet 3).
Proof. 
  exists 2; repeat (constructor).
Defined.

Definition s3 : (StringLang.string 3) :=
   [b; a; a; c; b].

Compute string_to_nat s3.
Compute nat_to_nat_list 3 209.

Definition get_string_function (n : nat) (f : nat -> option nat) :=
  fun (s : StringLang.string n)  => 
  match (f (string_to_nat s)) with
  | Some k => Some (nat_to_string n k)
  | None => None
  end.




(* Versão fraca, falta indexar por n *)
Definition program_equivalence p1 (p2 : StringLang.program 1) :=
  forall (f : nat -> option nat),
  (NatLang.partially_computable_by_p f p1) ->
  (StringLang.partially_computable_by_p 1 (get_string_function 1 f) p2).

Definition zero_prf : StringLang.alphabet 1.
Proof.
  exists 0.  constructor.
Defined.


(** Se eu conseguir fazer dessa forma, vai ser muito bom! *)
Definition get_string_program (p : NatLang.program) :
  ({p' | program_equivalence p p'}).
Proof.
Abort.

(* Tentar quebrar a prova em pedaços menores. *)
  





