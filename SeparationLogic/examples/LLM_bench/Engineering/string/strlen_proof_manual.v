Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Engineering.string Require Import strlen_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Engineering.string.string_lib.
Local Open Scope sac.

Lemma proof_of_strlen_entail_wit_1 : strlen_entail_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (store_string s_pre str).
  - split_pures.
    + dump_pre_spatial; auto.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; unfold string_length; apply Zlength_nonneg.
    + dump_pre_spatial; intros k Hk; lia.
Qed.

Lemma proof_of_strlen_entail_wit_2 : strlen_entail_wit_2.
Proof.
  pre_process.
  assert (Hi_lt : i < string_length str).
  { destruct (Z_lt_ge_dec i (string_length str)) as [Hlt | Hge]; auto.
    assert (i = string_length str) by lia.
    subst i.
    exfalso.
    apply H.
    unfold c_string, string_length.
    rewrite app_Znth2 by lia.
    replace (Zlength str - Zlength str) with 0 by lia.
    reflexivity. }
  split_pure_spatial.
  - unfold store_string; cancel.
  - split_pures.
    + dump_pre_spatial; auto.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial.
      intros k Hk.
      destruct (Z.eq_dec k i) as [Heq | Hneq].
      * subst k.
        unfold c_string in H.
        rewrite app_Znth1 in H by
          (unfold string_length in Hi_lt; lia).
        exact H.
      * apply H4; lia.
Qed.

Lemma proof_of_strlen_return_wit_1 : strlen_return_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - unfold store_string; cancel.
  - dump_pre_spatial.
    unfold string_length in *.
    unfold c_string in H.
    destruct H0 as [_ Hno].
    destruct (Z_lt_ge_dec i (Zlength str)) as [Hi | Hi].
    + rewrite app_Znth1 in H by lia.
      specialize (Hno i ltac:(lia)).
      contradiction.
    + lia.
Qed.
