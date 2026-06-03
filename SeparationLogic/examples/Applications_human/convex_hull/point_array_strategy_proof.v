Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.convex_hull Require Import point_array_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.convex_hull.convex_hull_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma point_array_strategy0_correctness : point_array_strategy0.
Proof.
  pre_process_default.
  Intros_p H1.
  subst l2.
  cancel.
Qed.


Lemma point_array_strategy1_correctness : point_array_strategy1.
Proof.
  pre_process_default.
  Intros_p H1.
  subst l2.
  cancel.
Qed.