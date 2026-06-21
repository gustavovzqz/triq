From Triq Require NatLang.
From Triq Require Import LanguagesCommon.
From Stdlib Require Import List.
Import ListNotations.


(** Definições de Estado Inicial *)
Definition is_initial_state (state_nat : NatLang.state) :=
state_nat Y = 0 /\ forall n, state_nat (Z n) = 0.
