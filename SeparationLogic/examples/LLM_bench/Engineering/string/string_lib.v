Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Definition all_ascii (s: list Z): Prop :=
  forall i, 0 <= i < Zlength s -> 0 <= Znth i s 0 <= 127.

Definition no_inner_nul (s: list Z): Prop :=
  forall i, 0 <= i < Zlength s -> Znth i s 0 <> 0.

Definition valid_string (s: list Z): Prop :=
  all_ascii s /\ no_inner_nul s.

Definition c_string (s: list Z): list Z :=
  s ++ [0].

Definition string_length (s: list Z): Z :=
  Zlength s.

Definition store_string (p: Z) (s: list Z): Assertion :=
  CharArray.full p (string_length s + 1) (c_string s).
