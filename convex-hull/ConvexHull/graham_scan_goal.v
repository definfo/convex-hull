Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.convex_hull.convex_hull_lib.
Require Import SimpleC.EE.QCP_demos_LLM.sll_merge_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope sac.
From SimpleC.EE.convex_hull Require Import point_array_strategy_goal.
From SimpleC.EE.convex_hull Require Import point_array_strategy_proof.
From SimpleC.EE.convex_hull Require Import safeexec_strategy_goal.
From SimpleC.EE.convex_hull Require Import safeexec_strategy_proof.

(*----- Function leftdown -----*)

Definition leftdown_safety_wit_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ (a_x_pre < b_x_pre) ”
  &&  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition leftdown_safety_wit_2 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ (a_x_pre < b_x_pre) ”
  &&  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition leftdown_safety_wit_3 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ (a_x_pre > b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ”
  &&  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition leftdown_safety_wit_4 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ (a_y_pre < b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ”
  &&  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition leftdown_safety_wit_5 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ (a_y_pre < b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ”
  &&  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition leftdown_safety_wit_6 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ (a_y_pre > b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ”
  &&  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition leftdown_safety_wit_7 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ (a_y_pre <= b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ”
  &&  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition leftdown_entail_wit_1 := 
  TT && emp 
|--
  TT && emp 
.

Definition leftdown_return_wit_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ (a_y_pre <= b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ”
  &&  emp
|--
  “ (0 = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
.

Definition leftdown_return_wit_2 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ (a_y_pre > b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ”
  &&  emp
|--
  “ (1 = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
.

Definition leftdown_return_wit_3 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ (a_y_pre < b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ”
  &&  emp
|--
  “ ((-1) = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
.

Definition leftdown_return_wit_4 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ (a_x_pre > b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ”
  &&  emp
|--
  “ (1 = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
.

Definition leftdown_return_wit_5 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ (a_x_pre < b_x_pre) ”
  &&  emp
|--
  “ ((-1) = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
.

(*----- Function cross_prod -----*)

Definition cross_prod_safety_wit_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_x_pre) ” 
  &&  “ (c_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_y_pre) ” 
  &&  “ (c_y_pre <= point_bound) ”
  &&  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((((b_x_pre - a_x_pre ) * (c_y_pre - a_y_pre ) ) - ((b_y_pre - a_y_pre ) * (c_x_pre - a_x_pre ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((b_x_pre - a_x_pre ) * (c_y_pre - a_y_pre ) ) - ((b_y_pre - a_y_pre ) * (c_x_pre - a_x_pre ) ) )) ”
.

Definition cross_prod_safety_wit_2 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_x_pre) ” 
  &&  “ (c_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_y_pre) ” 
  &&  “ (c_y_pre <= point_bound) ”
  &&  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ (((b_y_pre - a_y_pre ) * (c_x_pre - a_x_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((b_y_pre - a_y_pre ) * (c_x_pre - a_x_pre ) )) ”
.

Definition cross_prod_safety_wit_3 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_x_pre) ” 
  &&  “ (c_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_y_pre) ” 
  &&  “ (c_y_pre <= point_bound) ”
  &&  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((c_x_pre - a_x_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c_x_pre - a_x_pre )) ”
.

Definition cross_prod_safety_wit_4 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_x_pre) ” 
  &&  “ (c_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_y_pre) ” 
  &&  “ (c_y_pre <= point_bound) ”
  &&  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((b_y_pre - a_y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_y_pre - a_y_pre )) ”
.

Definition cross_prod_safety_wit_5 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_x_pre) ” 
  &&  “ (c_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_y_pre) ” 
  &&  “ (c_y_pre <= point_bound) ”
  &&  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ (((b_x_pre - a_x_pre ) * (c_y_pre - a_y_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((b_x_pre - a_x_pre ) * (c_y_pre - a_y_pre ) )) ”
.

Definition cross_prod_safety_wit_6 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_x_pre) ” 
  &&  “ (c_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_y_pre) ” 
  &&  “ (c_y_pre <= point_bound) ”
  &&  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((c_y_pre - a_y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c_y_pre - a_y_pre )) ”
.

Definition cross_prod_safety_wit_7 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_x_pre) ” 
  &&  “ (c_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_y_pre) ” 
  &&  “ (c_y_pre <= point_bound) ”
  &&  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((b_x_pre - a_x_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_x_pre - a_x_pre )) ”
.

Definition cross_prod_entail_wit_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_x_pre) ” 
  &&  “ (c_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_y_pre) ” 
  &&  “ (c_y_pre <= point_bound) ”
  &&  emp
|--
  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_x_pre) ” 
  &&  “ (c_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_y_pre) ” 
  &&  “ (c_y_pre <= point_bound) ”
  &&  emp
.

Definition cross_prod_return_wit_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_x_pre) ” 
  &&  “ (c_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_y_pre) ” 
  &&  “ (c_y_pre <= point_bound) ”
  &&  emp
|--
  “ ((((b_x_pre - a_x_pre ) * (c_y_pre - a_y_pre ) ) - ((b_y_pre - a_y_pre ) * (c_x_pre - a_x_pre ) ) ) = (point_cross_by_value (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre) (c_x_pre) (c_y_pre))) ”
  &&  emp
.

(*----- Function dot_prod -----*)

Definition dot_prod_safety_wit_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_x_pre) ” 
  &&  “ (c_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_y_pre) ” 
  &&  “ (c_y_pre <= point_bound) ”
  &&  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((((b_x_pre - a_x_pre ) * (c_x_pre - a_x_pre ) ) + ((b_y_pre - a_y_pre ) * (c_y_pre - a_y_pre ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((b_x_pre - a_x_pre ) * (c_x_pre - a_x_pre ) ) + ((b_y_pre - a_y_pre ) * (c_y_pre - a_y_pre ) ) )) ”
.

Definition dot_prod_safety_wit_2 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_x_pre) ” 
  &&  “ (c_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_y_pre) ” 
  &&  “ (c_y_pre <= point_bound) ”
  &&  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ (((b_y_pre - a_y_pre ) * (c_y_pre - a_y_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((b_y_pre - a_y_pre ) * (c_y_pre - a_y_pre ) )) ”
.

Definition dot_prod_safety_wit_3 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_x_pre) ” 
  &&  “ (c_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_y_pre) ” 
  &&  “ (c_y_pre <= point_bound) ”
  &&  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((c_y_pre - a_y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c_y_pre - a_y_pre )) ”
.

Definition dot_prod_safety_wit_4 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_x_pre) ” 
  &&  “ (c_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_y_pre) ” 
  &&  “ (c_y_pre <= point_bound) ”
  &&  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((b_y_pre - a_y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_y_pre - a_y_pre )) ”
.

Definition dot_prod_safety_wit_5 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_x_pre) ” 
  &&  “ (c_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_y_pre) ” 
  &&  “ (c_y_pre <= point_bound) ”
  &&  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ (((b_x_pre - a_x_pre ) * (c_x_pre - a_x_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((b_x_pre - a_x_pre ) * (c_x_pre - a_x_pre ) )) ”
.

Definition dot_prod_safety_wit_6 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_x_pre) ” 
  &&  “ (c_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_y_pre) ” 
  &&  “ (c_y_pre <= point_bound) ”
  &&  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((c_x_pre - a_x_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c_x_pre - a_x_pre )) ”
.

Definition dot_prod_safety_wit_7 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_x_pre) ” 
  &&  “ (c_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_y_pre) ” 
  &&  “ (c_y_pre <= point_bound) ”
  &&  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((b_x_pre - a_x_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_x_pre - a_x_pre )) ”
.

Definition dot_prod_entail_wit_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_x_pre) ” 
  &&  “ (c_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_y_pre) ” 
  &&  “ (c_y_pre <= point_bound) ”
  &&  emp
|--
  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_x_pre) ” 
  &&  “ (c_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_y_pre) ” 
  &&  “ (c_y_pre <= point_bound) ”
  &&  emp
.

Definition dot_prod_return_wit_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) ,
  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_x_pre) ” 
  &&  “ (c_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_y_pre) ” 
  &&  “ (c_y_pre <= point_bound) ”
  &&  emp
|--
  “ ((((b_x_pre - a_x_pre ) * (c_x_pre - a_x_pre ) ) + ((b_y_pre - a_y_pre ) * (c_y_pre - a_y_pre ) ) ) = (point_dot_by_value (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre) (c_x_pre) (c_y_pre))) ”
  &&  emp
.

(*----- Function cmp_polar -----*)

Definition cmp_polar_safety_wit_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (retval: Z) ,
  “ (retval = (point_cross_by_value (gp_x_pre) (gp_y_pre) (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre))) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "cr" ) )) # Int  |-> retval)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_safety_wit_2 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (retval: Z) ,
  “ (retval > 0) ” 
  &&  “ (retval = (point_cross_by_value (gp_x_pre) (gp_y_pre) (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre))) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "cr" ) )) # Int  |-> retval)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_safety_wit_3 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (retval: Z) ,
  “ (retval > 0) ” 
  &&  “ (retval = (point_cross_by_value (gp_x_pre) (gp_y_pre) (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre))) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "cr" ) )) # Int  |-> retval)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_safety_wit_4 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (retval: Z) ,
  “ (retval <= 0) ” 
  &&  “ (retval = (point_cross_by_value (gp_x_pre) (gp_y_pre) (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre))) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "cr" ) )) # Int  |-> retval)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_safety_wit_5 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (retval: Z) ,
  “ (retval < 0) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (retval = (point_cross_by_value (gp_x_pre) (gp_y_pre) (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre))) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "cr" ) )) # Int  |-> retval)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_safety_wit_6 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) ,
  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
|--
  “ ((((b_x_pre - a_x_pre ) * (gp_x_pre - a_x_pre ) ) + ((b_y_pre - a_y_pre ) * (gp_y_pre - a_y_pre ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((b_x_pre - a_x_pre ) * (gp_x_pre - a_x_pre ) ) + ((b_y_pre - a_y_pre ) * (gp_y_pre - a_y_pre ) ) )) ”
.

Definition cmp_polar_safety_wit_7 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) ,
  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
|--
  “ (((b_y_pre - a_y_pre ) * (gp_y_pre - a_y_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((b_y_pre - a_y_pre ) * (gp_y_pre - a_y_pre ) )) ”
.

Definition cmp_polar_safety_wit_8 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) ,
  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
|--
  “ ((gp_y_pre - a_y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (gp_y_pre - a_y_pre )) ”
.

Definition cmp_polar_safety_wit_9 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) ,
  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
|--
  “ ((b_y_pre - a_y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_y_pre - a_y_pre )) ”
.

Definition cmp_polar_safety_wit_10 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) ,
  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
|--
  “ (((b_x_pre - a_x_pre ) * (gp_x_pre - a_x_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((b_x_pre - a_x_pre ) * (gp_x_pre - a_x_pre ) )) ”
.

Definition cmp_polar_safety_wit_11 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) ,
  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
|--
  “ ((gp_x_pre - a_x_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (gp_x_pre - a_x_pre )) ”
.

Definition cmp_polar_safety_wit_12 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) ,
  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
|--
  “ ((b_x_pre - a_x_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_x_pre - a_x_pre )) ”
.

Definition cmp_polar_safety_wit_13 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) ,
  “ (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "cr" ) )) # Int  |-> cr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_safety_wit_14 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) ,
  “ (mid > 0) ” 
  &&  “ (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "cr" ) )) # Int  |-> cr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_safety_wit_15 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) ,
  “ (mid <= 0) ” 
  &&  “ (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "cr" ) )) # Int  |-> cr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_safety_wit_16 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) ,
  “ (mid < 0) ” 
  &&  “ (mid <= 0) ” 
  &&  “ (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "cr" ) )) # Int  |-> cr)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_safety_wit_17 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) ,
  “ (mid < 0) ” 
  &&  “ (mid <= 0) ” 
  &&  “ (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "cr" ) )) # Int  |-> cr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_safety_wit_18 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ (mid >= 0) ” 
  &&  “ (mid <= 0) ” 
  &&  “ (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "cr" ) )) # Int  |-> cr)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_safety_wit_19 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ (mid >= 0) ” 
  &&  “ (mid <= 0) ” 
  &&  “ (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "cr" ) )) # Int  |-> cr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_safety_wit_20 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) ,
  “ (a_x_pre > b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ (mid >= 0) ” 
  &&  “ (mid <= 0) ” 
  &&  “ (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "cr" ) )) # Int  |-> cr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_safety_wit_21 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) ,
  “ (a_y_pre < b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ (mid >= 0) ” 
  &&  “ (mid <= 0) ” 
  &&  “ (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "cr" ) )) # Int  |-> cr)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_safety_wit_22 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) ,
  “ (a_y_pre < b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ (mid >= 0) ” 
  &&  “ (mid <= 0) ” 
  &&  “ (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "cr" ) )) # Int  |-> cr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_safety_wit_23 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) ,
  “ (a_y_pre > b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ (mid >= 0) ” 
  &&  “ (mid <= 0) ” 
  &&  “ (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "cr" ) )) # Int  |-> cr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_safety_wit_24 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) ,
  “ (a_y_pre <= b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ (mid >= 0) ” 
  &&  “ (mid <= 0) ” 
  &&  “ (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "cr" ) )) # Int  |-> cr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_entail_wit_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) ,
  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  emp
|--
  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  emp
.

Definition cmp_polar_entail_wit_2 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (retval: Z) ,
  “ (retval >= 0) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (retval = (point_cross_by_value (gp_x_pre) (gp_y_pre) (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre))) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  emp
|--
  “ (retval = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  emp
.

Definition cmp_polar_entail_wit_3 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) ,
  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  emp
|--
  “ ((((b_x_pre - a_x_pre ) * (gp_x_pre - a_x_pre ) ) + ((b_y_pre - a_y_pre ) * (gp_y_pre - a_y_pre ) ) ) = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  emp
.

Definition cmp_polar_return_wit_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) ,
  “ (a_y_pre <= b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ (mid >= 0) ” 
  &&  “ (mid <= 0) ” 
  &&  “ (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  emp
|--
  “ (0 = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
.

Definition cmp_polar_return_wit_2 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) ,
  “ (a_y_pre > b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ (mid >= 0) ” 
  &&  “ (mid <= 0) ” 
  &&  “ (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  emp
|--
  “ (1 = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
.

Definition cmp_polar_return_wit_3 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) ,
  “ (a_y_pre < b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ (mid >= 0) ” 
  &&  “ (mid <= 0) ” 
  &&  “ (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  emp
|--
  “ ((-1) = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
.

Definition cmp_polar_return_wit_4 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) ,
  “ (a_x_pre > b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ (mid >= 0) ” 
  &&  “ (mid <= 0) ” 
  &&  “ (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  emp
|--
  “ (1 = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
.

Definition cmp_polar_return_wit_5 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ (mid >= 0) ” 
  &&  “ (mid <= 0) ” 
  &&  “ (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  emp
|--
  “ ((-1) = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
.

Definition cmp_polar_return_wit_6 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) ,
  “ (mid < 0) ” 
  &&  “ (mid <= 0) ” 
  &&  “ (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  emp
|--
  “ ((-1) = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
.

Definition cmp_polar_return_wit_7 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) ,
  “ (mid > 0) ” 
  &&  “ (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  emp
|--
  “ (1 = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
.

Definition cmp_polar_return_wit_8 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (retval: Z) ,
  “ (retval < 0) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (retval = (point_cross_by_value (gp_x_pre) (gp_y_pre) (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre))) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  emp
|--
  “ (1 = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
.

Definition cmp_polar_return_wit_9 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (retval: Z) ,
  “ (retval > 0) ” 
  &&  “ (retval = (point_cross_by_value (gp_x_pre) (gp_y_pre) (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre))) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  emp
|--
  “ ((-1) = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
.

Definition cmp_polar_partial_solve_wit_1_pure := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) ,
  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  ((( &( "cr" ) )) # Int  |->_)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (gp_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= gp_y_pre) ” 
  &&  “ (gp_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= gp_x_pre) ”
.

Definition cmp_polar_partial_solve_wit_1_aux := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) ,
  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  emp
|--
  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (gp_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= gp_y_pre) ” 
  &&  “ (gp_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= gp_x_pre) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  emp
.

Definition cmp_polar_partial_solve_wit_1 := cmp_polar_partial_solve_wit_1_pure -> cmp_polar_partial_solve_wit_1_aux.

(*----- Function build_hull_from_sorted_tail -----*)

Definition build_hull_from_sorted_tail_safety_wit_1 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) ,
  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (safeExec (equiv (empty_point_stack)) (build_hull (pivot0_low_level_spec) (l_low_level_spec)) X_low_level_spec ) ”
  &&  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_full hull_pre (tail_n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_hull_from_sorted_tail_safety_wit_2 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) ,
  “ (tail_n_pre < 0) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (safeExec (equiv (empty_point_stack)) (build_hull (pivot0_low_level_spec) (l_low_level_spec)) X_low_level_spec ) ”
  &&  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_full hull_pre (tail_n_pre + 1 ) )
|--
  “ False ”
.

Definition build_hull_from_sorted_tail_safety_wit_3 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) ,
  “ (tail_n_pre >= 0) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (safeExec (equiv (empty_point_stack)) (build_hull (pivot0_low_level_spec) (l_low_level_spec)) X_low_level_spec ) ”
  &&  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_full hull_pre (tail_n_pre + 1 ) )
|--
  “ (0 <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= 0) ”
.

Definition build_hull_from_sorted_tail_safety_wit_4 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) ,
  “ (tail_n_pre >= 0) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (safeExec (equiv (empty_point_stack)) (build_hull (pivot0_low_level_spec) (l_low_level_spec)) X_low_level_spec ) ”
  &&  ((&(((hull_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  (PointArray.undef_seg hull_pre 1 (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |->_)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
|--
  “ (0 <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= 0) ”
.

Definition build_hull_from_sorted_tail_safety_wit_5 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) ,
  “ (tail_n_pre >= 0) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (safeExec (equiv (empty_point_stack)) (build_hull (pivot0_low_level_spec) (l_low_level_spec)) X_low_level_spec ) ”
  &&  ((( &( "top" ) )) # Int  |->_)
  **  ((&(((hull_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  (PointArray.undef_seg hull_pre 1 (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_hull_from_sorted_tail_safety_wit_6 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) ,
  “ (tail_n_pre >= 0) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (safeExec (equiv (empty_point_stack)) (build_hull (pivot0_low_level_spec) (l_low_level_spec)) X_low_level_spec ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "top" ) )) # Int  |-> 0)
  **  ((&(((hull_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  (PointArray.undef_seg hull_pre 1 (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_hull_from_sorted_tail_safety_wit_7 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_hull_from_sorted_tail_safety_wit_8 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) ,
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  “ ((top - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top - 1 )) ”
.

Definition build_hull_from_sorted_tail_safety_wit_9 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) ,
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  “ ((top - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top - 1 )) ”
.

Definition build_hull_from_sorted_tail_safety_wit_10 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) ,
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_hull_from_sorted_tail_safety_wit_11 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) ,
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_hull_from_sorted_tail_safety_wit_12 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) (retval: Z)  __default_Point ,
  “ (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point)))))) ” 
  &&  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_hull_from_sorted_tail_safety_wit_13 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) (retval: Z)  __default_Point ,
  “ (retval <= 0) ” 
  &&  “ (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point)))))) ” 
  &&  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  “ ((top - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top - 1 )) ”
.

Definition build_hull_from_sorted_tail_safety_wit_14 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) (retval: Z)  __default_Point ,
  “ (retval > 0) ” 
  &&  “ (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point)))))) ” 
  &&  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  “ ((top + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top + 1 )) ”
.

Definition build_hull_from_sorted_tail_safety_wit_15 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) ,
  “ (top < 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  “ ((top + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top + 1 )) ”
.

Definition build_hull_from_sorted_tail_safety_wit_16 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point ,
  “ (top < 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i l_low_level_spec __default_Point))))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> (top + 1 ))
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition build_hull_from_sorted_tail_safety_wit_17 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) (retval: Z)  __default_Point ,
  “ (retval > 0) ” 
  &&  “ (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point)))))) ” 
  &&  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> (top + 1 ))
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition build_hull_from_sorted_tail_safety_wit_18 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) ,
  “ (i >= tail_n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_iter (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  “ ((top + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top + 1 )) ”
.

Definition build_hull_from_sorted_tail_safety_wit_19 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) ,
  “ (i >= tail_n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_iter (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_hull_from_sorted_tail_entail_wit_1 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) ,
  “ (tail_n_pre >= 0) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (safeExec (equiv (empty_point_stack)) (build_hull (pivot0_low_level_spec) (l_low_level_spec)) X_low_level_spec ) ”
  &&  ((&(((hull_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  (PointArray.undef_seg hull_pre 1 (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
|--
  EX (stk: (@list Point)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((0 + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_iter (l_low_level_spec) (0)) X_low_level_spec ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (0 + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (0 + 1 ) (tail_n_pre + 1 ) )
.

Definition build_hull_from_sorted_tail_entail_wit_2 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk_2: (@list Point)) (top: Z) (i: Z) ,
  “ (i < tail_n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk_2))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk_2)) ) ” 
  &&  “ (safeExec (equiv (stk_2)) (build_hull_c_iter (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk_2)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  EX (stk: (@list Point)) ,
  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
.

Definition build_hull_from_sorted_tail_entail_wit_3 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk_2: (@list Point)) (top: Z) (i: Z) (retval: Z)  __default_Point ,
  “ (retval <= 0) ” 
  &&  “ (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk_2)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk_2)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk_2)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk_2)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point)))))) ” 
  &&  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk_2))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk_2)) ) ” 
  &&  “ (safeExec (equiv (stk_2)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk_2)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  EX (stk: (@list Point)) ,
  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ ((top - 1 ) <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ (((top - 1 ) + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 ((top - 1 ) + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre ((top - 1 ) + 1 ) (tail_n_pre + 1 ) )
.

Definition build_hull_from_sorted_tail_entail_wit_4_1 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk_2: (@list Point)) (top: Z) (i: Z) (retval: Z)  __default_Point ,
  “ (retval > 0) ” 
  &&  “ (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk_2)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk_2)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk_2)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk_2)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point)))))) ” 
  &&  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk_2))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk_2)) ) ” 
  &&  “ (safeExec (equiv (stk_2)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk_2)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
|--
  EX (stk: (@list Point)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= tail_n_pre) ” 
  &&  “ ((top + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ (((top + 1 ) + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_iter (l_low_level_spec) ((i + 1 ))) X_low_level_spec ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 ((top + 1 ) + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
.

Definition build_hull_from_sorted_tail_entail_wit_4_2 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk_2: (@list Point)) (top: Z) (i: Z)  __default_Point ,
  “ (top < 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk_2))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk_2)) ) ” 
  &&  “ (safeExec (equiv (stk_2)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i l_low_level_spec __default_Point))))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk_2)) )
|--
  EX (stk: (@list Point)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= tail_n_pre) ” 
  &&  “ ((top + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ (((top + 1 ) + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_iter (l_low_level_spec) ((i + 1 ))) X_low_level_spec ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 ((top + 1 ) + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
.

Definition build_hull_from_sorted_tail_return_wit_1 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk_2: (@list Point)) (top: Z) (i: Z) ,
  “ (i >= tail_n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk_2))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk_2)) ) ” 
  &&  “ (safeExec (equiv (stk_2)) (build_hull_c_iter (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk_2)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  EX (stk: (@list Point)) ,
  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (return (tt)) X_low_level_spec ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
.

Definition build_hull_from_sorted_tail_partial_solve_wit_1 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) ,
  “ (tail_n_pre >= 0) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (safeExec (equiv (empty_point_stack)) (build_hull (pivot0_low_level_spec) (l_low_level_spec)) X_low_level_spec ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_full hull_pre (tail_n_pre + 1 ) )
|--
  “ (tail_n_pre >= 0) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (safeExec (equiv (empty_point_stack)) (build_hull (pivot0_low_level_spec) (l_low_level_spec)) X_low_level_spec ) ”
  &&  ((&(((hull_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |->_)
  **  (PointArray.undef_seg hull_pre 1 (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |->_)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
.

Definition build_hull_from_sorted_tail_partial_solve_wit_2 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point ,
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point))))
  **  (PointArray.missing_i hull_pre (top - 1 ) 0 (top + 1 ) (rev (stk)) )
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point))))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
.

Definition build_hull_from_sorted_tail_partial_solve_wit_3 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point ,
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point))))
  **  (PointArray.missing_i hull_pre (top - 1 ) 0 (top + 1 ) (rev (stk)) )
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point))))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
.

Definition build_hull_from_sorted_tail_partial_solve_wit_4 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point ,
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth (top - 0 ) (rev (stk)) __default_Point))))
  **  (PointArray.missing_i hull_pre top 0 (top + 1 ) (rev (stk)) )
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth (top - 0 ) (rev (stk)) __default_Point))))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
.

Definition build_hull_from_sorted_tail_partial_solve_wit_5 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point ,
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth (top - 0 ) (rev (stk)) __default_Point))))
  **  (PointArray.missing_i hull_pre top 0 (top + 1 ) (rev (stk)) )
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth (top - 0 ) (rev (stk)) __default_Point))))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
.

Definition build_hull_from_sorted_tail_partial_solve_wit_6 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point ,
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n_pre l_low_level_spec )
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
.

Definition build_hull_from_sorted_tail_partial_solve_wit_7 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point ,
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n_pre l_low_level_spec )
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
.

Definition build_hull_from_sorted_tail_partial_solve_wit_8_pure := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point ,
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  “ ((point_y ((Znth i l_low_level_spec __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth i l_low_level_spec __default_Point)))) ” 
  &&  “ ((point_x ((Znth i l_low_level_spec __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth i l_low_level_spec __default_Point)))) ” 
  &&  “ ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ” 
  &&  “ ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ” 
  &&  “ ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ” 
  &&  “ ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ”
.

Definition build_hull_from_sorted_tail_partial_solve_wit_8_aux := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point ,
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  “ ((point_y ((Znth i l_low_level_spec __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth i l_low_level_spec __default_Point)))) ” 
  &&  “ ((point_x ((Znth i l_low_level_spec __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth i l_low_level_spec __default_Point)))) ” 
  &&  “ ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ” 
  &&  “ ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ” 
  &&  “ ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ” 
  &&  “ ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ” 
  &&  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
.

Definition build_hull_from_sorted_tail_partial_solve_wit_8 := build_hull_from_sorted_tail_partial_solve_wit_8_pure -> build_hull_from_sorted_tail_partial_solve_wit_8_aux.

Definition build_hull_from_sorted_tail_partial_solve_wit_9 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point ,
  “ (top < 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  “ (top < 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n_pre l_low_level_spec )
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i l_low_level_spec __default_Point))))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
.

Definition build_hull_from_sorted_tail_partial_solve_wit_10 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) ,
  “ (top < 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  “ (top < 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |->_)
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
.

Definition build_hull_from_sorted_tail_partial_solve_wit_11 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) (retval: Z)  __default_Point ,
  “ (retval > 0) ” 
  &&  “ (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point)))))) ” 
  &&  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  “ (retval > 0) ” 
  &&  “ (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point)))))) ” 
  &&  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n_pre l_low_level_spec )
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
.

Definition build_hull_from_sorted_tail_partial_solve_wit_12 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) (retval: Z)  __default_Point ,
  “ (retval > 0) ” 
  &&  “ (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point)))))) ” 
  &&  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
|--
  “ (retval > 0) ” 
  &&  “ (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point)))))) ” 
  &&  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |->_)
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
.

Definition build_hull_from_sorted_tail_partial_solve_wit_13 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) (retval: Z)  __default_Point ,
  “ (retval > 0) ” 
  &&  “ (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point)))))) ” 
  &&  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
|--
  “ (retval > 0) ” 
  &&  “ (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point)))))) ” 
  &&  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n_pre l_low_level_spec )
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
.

Definition build_hull_from_sorted_tail_partial_solve_wit_14 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point ,
  “ (top < 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
|--
  “ (top < 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n_pre l_low_level_spec )
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |->_)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
.

(*----- Function swap_points -----*)

Definition swap_points_entail_wit_1 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point ,
  “ (i_pre < j_pre) ” 
  &&  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (i_pre <> j_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ”
  &&  (PointArray.full pts_pre n_pre pts_l )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ”
  &&  ((&(((pts_pre + (i_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i_pre pts_l __default_Point).(x) ))
  **  ((&(((pts_pre + (i_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i_pre pts_l __default_Point).(y) ))
  **  ((&(((pts_pre + (j_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth j_pre pts_l __default_Point).(x) ))
  **  ((&(((pts_pre + (j_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth j_pre pts_l __default_Point).(y) ))
  **  (PointArray.seg pts_pre 0 i_pre (sublist (0) (i_pre) (pts_l)) )
  **  (PointArray.seg pts_pre (i_pre + 1 ) j_pre (sublist ((i_pre + 1 )) (j_pre) (pts_l)) )
  **  (PointArray.seg pts_pre (j_pre + 1 ) n_pre (sublist ((j_pre + 1 )) (n_pre) (pts_l)) )
.

Definition swap_points_entail_wit_2 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point ,
  “ (i_pre >= j_pre) ” 
  &&  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (i_pre <> j_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ”
  &&  (PointArray.full pts_pre n_pre pts_l )
|--
  “ (0 <= j_pre) ” 
  &&  “ (j_pre < i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ”
  &&  ((&(((pts_pre + (i_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i_pre pts_l __default_Point).(x) ))
  **  ((&(((pts_pre + (i_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i_pre pts_l __default_Point).(y) ))
  **  ((&(((pts_pre + (j_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth j_pre pts_l __default_Point).(x) ))
  **  ((&(((pts_pre + (j_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth j_pre pts_l __default_Point).(y) ))
  **  (PointArray.seg pts_pre 0 j_pre (sublist (0) (j_pre) (pts_l)) )
  **  (PointArray.seg pts_pre (j_pre + 1 ) i_pre (sublist ((j_pre + 1 )) (i_pre) (pts_l)) )
  **  (PointArray.seg pts_pre (i_pre + 1 ) n_pre (sublist ((i_pre + 1 )) (n_pre) (pts_l)) )
.

Definition swap_points_return_wit_1 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ”
  &&  ((&(((pts_pre + (i_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth j_pre pts_l __default_Point).(x) ))
  **  ((&(((pts_pre + (i_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth j_pre pts_l __default_Point).(y) ))
  **  ((&(((pts_pre + (j_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i_pre pts_l __default_Point).(x) ))
  **  ((&(((pts_pre + (j_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i_pre pts_l __default_Point).(y) ))
  **  (PointArray.seg pts_pre 0 i_pre (sublist (0) (i_pre) (pts_l)) )
  **  (PointArray.seg pts_pre (i_pre + 1 ) j_pre (sublist ((i_pre + 1 )) (j_pre) (pts_l)) )
  **  (PointArray.seg pts_pre (j_pre + 1 ) n_pre (sublist ((j_pre + 1 )) (n_pre) (pts_l)) )
|--
  “ ((Zlength (pts_l)) = n_pre) ”
  &&  (PointArray.full pts_pre n_pre (point_swap (pts_l) (i_pre) (j_pre)) )
.

Definition swap_points_return_wit_2 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point ,
  “ (0 <= j_pre) ” 
  &&  “ (j_pre < i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ”
  &&  ((&(((pts_pre + (i_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth j_pre pts_l __default_Point).(x) ))
  **  ((&(((pts_pre + (i_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth j_pre pts_l __default_Point).(y) ))
  **  ((&(((pts_pre + (j_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i_pre pts_l __default_Point).(x) ))
  **  ((&(((pts_pre + (j_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i_pre pts_l __default_Point).(y) ))
  **  (PointArray.seg pts_pre 0 j_pre (sublist (0) (j_pre) (pts_l)) )
  **  (PointArray.seg pts_pre (j_pre + 1 ) i_pre (sublist ((j_pre + 1 )) (i_pre) (pts_l)) )
  **  (PointArray.seg pts_pre (i_pre + 1 ) n_pre (sublist ((i_pre + 1 )) (n_pre) (pts_l)) )
|--
  “ ((Zlength (pts_l)) = n_pre) ”
  &&  (PointArray.full pts_pre n_pre (point_swap (pts_l) (i_pre) (j_pre)) )
.

(*----- Function partition_polar_points -----*)

Definition partition_polar_points_safety_wit_1 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "pivot_y" ) )) # Int  |-> ((Znth high_pre pts_l __default_Point).(y) ))
  **  ((( &( "pivot_x" ) )) # Int  |-> ((Znth high_pre pts_l __default_Point).(x) ))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((&(((pts_pre + (high_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth high_pre pts_l __default_Point).(x) ))
  **  ((&(((pts_pre + (high_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth high_pre pts_l __default_Point).(y) ))
  **  (PointArray.missing_i pts_pre high_pre 0 n_pre pts_l )
|--
  “ ((low_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (low_pre - 1 )) ”
.

Definition partition_polar_points_safety_wit_2 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "pivot_y" ) )) # Int  |-> ((Znth high_pre pts_l __default_Point).(y) ))
  **  ((( &( "pivot_x" ) )) # Int  |-> ((Znth high_pre pts_l __default_Point).(x) ))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((&(((pts_pre + (high_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth high_pre pts_l __default_Point).(x) ))
  **  ((&(((pts_pre + (high_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth high_pre pts_l __default_Point).(y) ))
  **  (PointArray.missing_i pts_pre high_pre 0 n_pre pts_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_polar_points_safety_wit_3 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z) (retval: Z)  __default_Point ,
  “ (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk (ax) (ay))) ((point_mk (pivot_x) (pivot_y))))) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= j) ” 
  &&  “ (j < high_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "c" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "ax" ) )) # Int  |-> ax)
  **  ((( &( "ay" ) )) # Int  |-> ay)
  **  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition partition_polar_points_safety_wit_4 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z) (retval: Z)  __default_Point ,
  “ (retval <= 0) ” 
  &&  “ (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk (ax) (ay))) ((point_mk (pivot_x) (pivot_y))))) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= j) ” 
  &&  “ (j < high_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "c" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "ax" ) )) # Int  |-> ax)
  **  ((( &( "ay" ) )) # Int  |-> ay)
  **  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_polar_points_safety_wit_5 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z) (retval: Z)  __default_Point ,
  “ (retval > 0) ” 
  &&  “ (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk (ax) (ay))) ((point_mk (pivot_x) (pivot_y))))) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= j) ” 
  &&  “ (j < high_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition partition_polar_points_safety_wit_6 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z) (retval: Z)  __default_Point ,
  “ ((i + 1 ) = j) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk (ax) (ay))) ((point_mk (pivot_x) (pivot_y))))) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= j) ” 
  &&  “ (j < high_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition partition_polar_points_safety_wit_7 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z) (retval: Z)  __default_Point ,
  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((i + 1 ) <> j) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk (ax) (ay))) ((point_mk (pivot_x) (pivot_y))))) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= j) ” 
  &&  “ (j < high_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts_pre n_pre (point_swap (pts_cur) ((i + 1 )) (j)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition partition_polar_points_safety_wit_8 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point ,
  “ (j >= high_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_polar_points_safety_wit_9 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point ,
  “ (j >= high_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_polar_points_safety_wit_10 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point ,
  “ ((i + 1 ) <> high_pre) ” 
  &&  “ (j >= high_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_polar_points_safety_wit_11 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point ,
  “ ((i + 1 ) <> high_pre) ” 
  &&  “ (j >= high_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_polar_points_safety_wit_12 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point ,
  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((i + 1 ) <> high_pre) ” 
  &&  “ (j >= high_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts_pre n_pre (point_swap (pts_cur) ((i + 1 )) (high_pre)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_polar_points_safety_wit_13 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point ,
  “ ((i + 1 ) = high_pre) ” 
  &&  “ (j >= high_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_polar_points_safety_wit_14 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point ,
  “ ((i + 1 ) = high_pre) ” 
  &&  “ (j >= high_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_polar_points_safety_wit_15 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point ,
  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((i + 1 ) <> high_pre) ” 
  &&  “ (j >= high_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts_pre n_pre (point_swap (pts_cur) ((i + 1 )) (high_pre)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_polar_points_entail_wit_1 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  (PointArray.full pts_pre n_pre pts_l )
|--
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  ((&(((pts_pre + (high_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth high_pre pts_l __default_Point).(x) ))
  **  ((&(((pts_pre + (high_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth high_pre pts_l __default_Point).(y) ))
  **  (PointArray.missing_i pts_pre high_pre 0 n_pre pts_l )
.

Definition partition_polar_points_entail_wit_2 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  ((&(((pts_pre + (high_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth high_pre pts_l __default_Point).(x) ))
  **  ((&(((pts_pre + (high_pre * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth high_pre pts_l __default_Point).(y) ))
  **  (PointArray.missing_i pts_pre high_pre 0 n_pre pts_l )
|--
  EX (pts_cur: (@list Point)) ,
  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= (low_pre - 1 )) ” 
  &&  “ ((low_pre - 1 ) < low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = ((Znth high_pre pts_l __default_Point).(x) )) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = ((Znth high_pre pts_l __default_Point).(y) )) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (((Znth high_pre pts_l __default_Point).(x) )) (((Znth high_pre pts_l __default_Point).(y) ))) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (((Znth high_pre pts_l __default_Point).(x) )) (((Znth high_pre pts_l __default_Point).(y) ))) (low_pre - 1 ) low_pre ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
.

Definition partition_polar_points_entail_wit_3 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point))  __default_Point ,
  “ (j < high_pre) ” 
  &&  “ ((Zlength (pts_cur_2)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur_2 ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur_2 )
|--
  EX (pts_cur: (@list Point)) ,
  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= j) ” 
  &&  “ (j < high_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((&(((pts_pre + (j * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth j pts_cur __default_Point).(x) ))
  **  ((&(((pts_pre + (j * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth j pts_cur __default_Point).(y) ))
  **  (PointArray.missing_i pts_pre j 0 n_pre pts_cur )
.

Definition partition_polar_points_entail_wit_4 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z)  __default_Point ,
  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= j) ” 
  &&  “ (j < high_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((&(((pts_pre + (j * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth j pts_cur __default_Point).(x) ))
  **  ((&(((pts_pre + (j * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth j pts_cur __default_Point).(y) ))
  **  (PointArray.missing_i pts_pre j 0 n_pre pts_cur )
|--
  EX (pts_cur_2: (@list Point)) ,
  “ ((Zlength (pts_cur_2)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= j) ” 
  &&  “ (j < high_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur_2 __default_Point).(x) ) = ((Znth j pts_cur __default_Point).(x) )) ” 
  &&  “ (((Znth j pts_cur_2 __default_Point).(y) ) = ((Znth j pts_cur __default_Point).(y) )) ” 
  &&  “ (PointCoordsBound pts_cur_2 ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (((Znth j pts_cur __default_Point).(x) )) (((Znth j pts_cur __default_Point).(y) ))) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur_2 )
.

Definition partition_polar_points_entail_wit_5_1 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur_2: (@list Point)) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z) (retval: Z)  __default_Point ,
  “ ((Zlength (pts_cur_2)) = n_pre) ” 
  &&  “ ((i + 1 ) <> j) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk (ax) (ay))) ((point_mk (pivot_x) (pivot_y))))) ” 
  &&  “ ((Zlength (pts_cur_2)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= j) ” 
  &&  “ (j < high_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur_2 __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur_2 __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur_2 ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts_pre n_pre (point_swap (pts_cur_2) ((i + 1 )) (j)) )
|--
  EX (pts_cur: (@list Point)) ,
  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < (j + 1 )) ” 
  &&  “ ((j + 1 ) <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) (i + 1 ) (j + 1 ) ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
.

Definition partition_polar_points_entail_wit_5_2 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur_2: (@list Point)) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z) (retval: Z)  __default_Point ,
  “ ((i + 1 ) = j) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk (ax) (ay))) ((point_mk (pivot_x) (pivot_y))))) ” 
  &&  “ ((Zlength (pts_cur_2)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= j) ” 
  &&  “ (j < high_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur_2 __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur_2 __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur_2 ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur_2 )
|--
  EX (pts_cur: (@list Point)) ,
  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < (j + 1 )) ” 
  &&  “ ((j + 1 ) <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) (i + 1 ) (j + 1 ) ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
.

Definition partition_polar_points_entail_wit_5_3 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur_2: (@list Point)) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z) (retval: Z)  __default_Point ,
  “ (retval > 0) ” 
  &&  “ (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk (ax) (ay))) ((point_mk (pivot_x) (pivot_y))))) ” 
  &&  “ ((Zlength (pts_cur_2)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= j) ” 
  &&  “ (j < high_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur_2 __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur_2 __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur_2 ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur_2 )
|--
  EX (pts_cur: (@list Point)) ,
  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < (j + 1 )) ” 
  &&  “ ((j + 1 ) <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i (j + 1 ) ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
.

Definition partition_polar_points_return_wit_1 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point ,
  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((i + 1 ) <> high_pre) ” 
  &&  “ (j >= high_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts_pre n_pre (point_swap (pts_cur) ((i + 1 )) (high_pre)) )
|--
  EX (pts_out: (@list Point)) ,
  “ (low_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= high_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out low_pre high_pre ) ” 
  &&  “ (PointPolarPartitionedAt (point_mk (gx_pre) (gy_pre)) pts_out low_pre high_pre (i + 1 ) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
.

Definition partition_polar_points_return_wit_2 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point ,
  “ ((i + 1 ) = high_pre) ” 
  &&  “ (j >= high_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
|--
  EX (pts_out: (@list Point)) ,
  “ (low_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= high_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out low_pre high_pre ) ” 
  &&  “ (PointPolarPartitionedAt (point_mk (gx_pre) (gy_pre)) pts_out low_pre high_pre (i + 1 ) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
.

Definition partition_polar_points_partial_solve_wit_1_pure := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z)  __default_Point ,
  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= j) ” 
  &&  “ (j < high_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "ax" ) )) # Int  |-> ax)
  **  ((( &( "ay" ) )) # Int  |-> ay)
  **  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ”
.

Definition partition_polar_points_partial_solve_wit_1_aux := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z)  __default_Point ,
  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= j) ” 
  &&  “ (j < high_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= j) ” 
  &&  “ (j < high_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
.

Definition partition_polar_points_partial_solve_wit_1 := partition_polar_points_partial_solve_wit_1_pure -> partition_polar_points_partial_solve_wit_1_aux.

Definition partition_polar_points_partial_solve_wit_2_pure := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z) (retval: Z)  __default_Point ,
  “ ((i + 1 ) <> j) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk (ax) (ay))) ((point_mk (pivot_x) (pivot_y))))) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= j) ” 
  &&  “ (j < high_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "c" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "ax" ) )) # Int  |-> ax)
  **  ((( &( "ay" ) )) # Int  |-> ay)
  **  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ ((i + 1 ) <> j) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ”
.

Definition partition_polar_points_partial_solve_wit_2_aux := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z) (retval: Z)  __default_Point ,
  “ ((i + 1 ) <> j) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk (ax) (ay))) ((point_mk (pivot_x) (pivot_y))))) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= j) ” 
  &&  “ (j < high_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ ((i + 1 ) <> j) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((i + 1 ) <> j) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk (ax) (ay))) ((point_mk (pivot_x) (pivot_y))))) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= j) ” 
  &&  “ (j < high_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
.

Definition partition_polar_points_partial_solve_wit_2 := partition_polar_points_partial_solve_wit_2_pure -> partition_polar_points_partial_solve_wit_2_aux.

Definition partition_polar_points_partial_solve_wit_3_pure := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point ,
  “ ((i + 1 ) <> high_pre) ” 
  &&  “ (j >= high_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((i + 1 ) <> high_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ”
.

Definition partition_polar_points_partial_solve_wit_3_aux := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point ,
  “ ((i + 1 ) <> high_pre) ” 
  &&  “ (j >= high_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((i + 1 ) <> high_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((i + 1 ) <> high_pre) ” 
  &&  “ (j >= high_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
.

Definition partition_polar_points_partial_solve_wit_3 := partition_polar_points_partial_solve_wit_3_pure -> partition_polar_points_partial_solve_wit_3_aux.

(*----- Function quicksort_polar_points -----*)

Definition quicksort_polar_points_safety_wit_1 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) ,
  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPolarPartitionedAt (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ ((retval - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - 1 )) ”
.

Definition quicksort_polar_points_safety_wit_2 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) ,
  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPolarPartitionedAt (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_polar_points_safety_wit_3 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) ,
  “ (retval >= right_pre) ” 
  &&  “ (retval <= left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPolarPartitionedAt (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ False ”
.

Definition quicksort_polar_points_safety_wit_4 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (pts_out_2: (@list Point)) ,
  “ (retval < right_pre) ” 
  &&  “ ((Zlength (pts_out_2)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out_2 ) ” 
  &&  “ (PointPermutation pts_out pts_out_2 ) ” 
  &&  “ (PointSameOutsideRange pts_out pts_out_2 left_pre (retval - 1 ) ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre (retval - 1 ) ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPolarPartitionedAt (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out_2 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition quicksort_polar_points_safety_wit_5 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (pts_out_2: (@list Point)) ,
  “ (retval < right_pre) ” 
  &&  “ ((Zlength (pts_out_2)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out_2 ) ” 
  &&  “ (PointPermutation pts_out pts_out_2 ) ” 
  &&  “ (PointSameOutsideRange pts_out pts_out_2 left_pre (retval - 1 ) ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre (retval - 1 ) ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPolarPartitionedAt (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out_2 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_polar_points_safety_wit_6 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) ,
  “ (retval < right_pre) ” 
  &&  “ (retval <= left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPolarPartitionedAt (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition quicksort_polar_points_safety_wit_7 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) ,
  “ (retval < right_pre) ” 
  &&  “ (retval <= left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPolarPartitionedAt (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_polar_points_return_wit_1 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (pts_out_4: (@list Point)) ,
  “ ((Zlength (pts_out_4)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out_4 ) ” 
  &&  “ (PointPermutation pts_out_3 pts_out_4 ) ” 
  &&  “ (PointSameOutsideRange pts_out_3 pts_out_4 (retval + 1 ) right_pre ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx_pre) (gy_pre)) pts_out_4 (retval + 1 ) right_pre ) ” 
  &&  “ (retval < right_pre) ” 
  &&  “ ((Zlength (pts_out_3)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out_3 ) ” 
  &&  “ (PointPermutation pts_out_2 pts_out_3 ) ” 
  &&  “ (PointSameOutsideRange pts_out_2 pts_out_3 left_pre (retval - 1 ) ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out_2)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out_2 ) ” 
  &&  “ (PointPermutation pts_l pts_out_2 ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out_2 left_pre right_pre ) ” 
  &&  “ (PointPolarPartitionedAt (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out_4 )
|--
  EX (pts_out: (@list Point)) ,
  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
.

Definition quicksort_polar_points_return_wit_2 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) ,
  “ ((Zlength (pts_out_3)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out_3 ) ” 
  &&  “ (PointPermutation pts_out_2 pts_out_3 ) ” 
  &&  “ (PointSameOutsideRange pts_out_2 pts_out_3 (retval + 1 ) right_pre ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx_pre) (gy_pre)) pts_out_3 (retval + 1 ) right_pre ) ” 
  &&  “ (retval < right_pre) ” 
  &&  “ (retval <= left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out_2)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out_2 ) ” 
  &&  “ (PointPermutation pts_l pts_out_2 ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out_2 left_pre right_pre ) ” 
  &&  “ (PointPolarPartitionedAt (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out_3 )
|--
  EX (pts_out: (@list Point)) ,
  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
.

Definition quicksort_polar_points_return_wit_3 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) ,
  “ (retval >= right_pre) ” 
  &&  “ ((Zlength (pts_out_3)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out_3 ) ” 
  &&  “ (PointPermutation pts_out_2 pts_out_3 ) ” 
  &&  “ (PointSameOutsideRange pts_out_2 pts_out_3 left_pre (retval - 1 ) ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out_2)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out_2 ) ” 
  &&  “ (PointPermutation pts_l pts_out_2 ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out_2 left_pre right_pre ) ” 
  &&  “ (PointPolarPartitionedAt (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out_3 )
|--
  EX (pts_out: (@list Point)) ,
  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
.

Definition quicksort_polar_points_return_wit_4 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) ,
  “ (left_pre >= right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  (PointArray.full pts_pre n_pre pts_l )
|--
  EX (pts_out: (@list Point)) ,
  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
.

Definition quicksort_polar_points_partial_solve_wit_1_pure := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) ,
  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  (PointArray.full pts_pre n_pre pts_l )
|--
  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
.

Definition quicksort_polar_points_partial_solve_wit_1_aux := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) ,
  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  (PointArray.full pts_pre n_pre pts_l )
|--
  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  (PointArray.full pts_pre n_pre pts_l )
.

Definition quicksort_polar_points_partial_solve_wit_1 := quicksort_polar_points_partial_solve_wit_1_pure -> quicksort_polar_points_partial_solve_wit_1_aux.

Definition quicksort_polar_points_partial_solve_wit_2_pure := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) ,
  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPolarPartitionedAt (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= (retval - 1 )) ” 
  &&  “ ((retval - 1 ) < n_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
.

Definition quicksort_polar_points_partial_solve_wit_2_aux := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) ,
  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPolarPartitionedAt (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= (retval - 1 )) ” 
  &&  “ ((retval - 1 ) < n_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPolarPartitionedAt (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
.

Definition quicksort_polar_points_partial_solve_wit_2 := quicksort_polar_points_partial_solve_wit_2_pure -> quicksort_polar_points_partial_solve_wit_2_aux.

Definition quicksort_polar_points_partial_solve_wit_3_pure := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out: (@list Point)) ,
  “ (retval < right_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_out_2 pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_out_2 pts_out left_pre (retval - 1 ) ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx_pre) (gy_pre)) pts_out left_pre (retval - 1 ) ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out_2)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out_2 ) ” 
  &&  “ (PointPermutation pts_l pts_out_2 ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out_2 left_pre right_pre ) ” 
  &&  “ (PointPolarPartitionedAt (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
.

Definition quicksort_polar_points_partial_solve_wit_3_aux := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out: (@list Point)) ,
  “ (retval < right_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_out_2 pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_out_2 pts_out left_pre (retval - 1 ) ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx_pre) (gy_pre)) pts_out left_pre (retval - 1 ) ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out_2)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out_2 ) ” 
  &&  “ (PointPermutation pts_l pts_out_2 ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out_2 left_pre right_pre ) ” 
  &&  “ (PointPolarPartitionedAt (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (retval < right_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_out_2 pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_out_2 pts_out left_pre (retval - 1 ) ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx_pre) (gy_pre)) pts_out left_pre (retval - 1 ) ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out_2)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out_2 ) ” 
  &&  “ (PointPermutation pts_l pts_out_2 ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out_2 left_pre right_pre ) ” 
  &&  “ (PointPolarPartitionedAt (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
.

Definition quicksort_polar_points_partial_solve_wit_3 := quicksort_polar_points_partial_solve_wit_3_pure -> quicksort_polar_points_partial_solve_wit_3_aux.

Definition quicksort_polar_points_partial_solve_wit_4_pure := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) ,
  “ (retval < right_pre) ” 
  &&  “ (retval <= left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPolarPartitionedAt (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
.

Definition quicksort_polar_points_partial_solve_wit_4_aux := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) ,
  “ (retval < right_pre) ” 
  &&  “ (retval <= left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPolarPartitionedAt (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (retval < right_pre) ” 
  &&  “ (retval <= left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPolarPartitionedAt (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
.

Definition quicksort_polar_points_partial_solve_wit_4 := quicksort_polar_points_partial_solve_wit_4_pure -> quicksort_polar_points_partial_solve_wit_4_aux.

(*----- Function graham_scan -----*)

Definition graham_scan_safety_wit_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((( &( "pivot_idx" ) )) # Int  |->_)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  (PointArray.full pts_pre n_pre pts_l )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition graham_scan_safety_wit_2 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "pivot_idx" ) )) # Int  |-> 0)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  (PointArray.full pts_pre n_pre pts_l )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition graham_scan_safety_wit_3 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z) (retval: Z)  __default_Point ,
  “ (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth i pts_l __default_Point)))) ((point_y ((Znth i pts_l __default_Point)))))) ((point_mk ((point_x ((Znth pivot_idx pts_l __default_Point)))) ((point_y ((Znth pivot_idx pts_l __default_Point)))))))) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  ((( &( "b_y_val" ) )) # Int  |-> (point_y ((Znth pivot_idx pts_l __default_Point))))
  **  ((( &( "bx" ) )) # Int  |-> (point_x ((Znth pivot_idx pts_l __default_Point))))
  **  ((( &( "ay" ) )) # Int  |-> (point_y ((Znth i pts_l __default_Point))))
  **  ((( &( "ax" ) )) # Int  |-> (point_x ((Znth i pts_l __default_Point))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition graham_scan_safety_wit_4 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z) (retval: Z)  __default_Point ,
  “ (retval >= 0) ” 
  &&  “ (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth i pts_l __default_Point)))) ((point_y ((Znth i pts_l __default_Point)))))) ((point_mk ((point_x ((Znth pivot_idx pts_l __default_Point)))) ((point_y ((Znth pivot_idx pts_l __default_Point)))))))) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.undef_full hull_pre n )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition graham_scan_safety_wit_5 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z) (retval: Z)  __default_Point ,
  “ (retval < 0) ” 
  &&  “ (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth i pts_l __default_Point)))) ((point_y ((Znth i pts_l __default_Point)))))) ((point_mk ((point_x ((Znth pivot_idx pts_l __default_Point)))) ((point_y ((Znth pivot_idx pts_l __default_Point)))))))) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_idx" ) )) # Int  |-> i)
  **  (PointArray.undef_full hull_pre n )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition graham_scan_safety_wit_6 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z) ,
  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition graham_scan_safety_wit_7 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z) ,
  “ (pivot_idx <> 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition graham_scan_safety_wit_8 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z) ,
  “ (pivot_idx = 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((( &( "gx" ) )) # Int  |->_)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition graham_scan_safety_wit_9 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z) ,
  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (pivot_idx <> 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((( &( "gx" ) )) # Int  |->_)
  **  (PointArray.full pts_pre n (point_swap (pts_l) (0) (pivot_idx)) )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition graham_scan_safety_wit_10 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z)  __default_Point ,
  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (pivot_idx <> 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((( &( "gy" ) )) # Int  |->_)
  **  (PointArray.full pts_pre n (point_swap (pts_l) (0) (pivot_idx)) )
  **  ((( &( "gx" ) )) # Int  |-> (point_x ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition graham_scan_safety_wit_11 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z)  __default_Point ,
  “ (pivot_idx = 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((( &( "gy" ) )) # Int  |->_)
  **  (PointArray.full pts_pre n pts_l )
  **  ((( &( "gx" ) )) # Int  |-> (point_x ((Znth 0 pts_l __default_Point))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition graham_scan_safety_wit_12 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z)  __default_Point ,
  “ (pivot_idx = 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  ((( &( "gy" ) )) # Int  |-> (point_y ((Znth 0 pts_l __default_Point))))
  **  ((( &( "gx" ) )) # Int  |-> (point_x ((Znth 0 pts_l __default_Point))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.undef_full hull_pre n )
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition graham_scan_safety_wit_13 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z)  __default_Point ,
  “ (pivot_idx = 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  ((( &( "gy" ) )) # Int  |-> (point_y ((Znth 0 pts_l __default_Point))))
  **  ((( &( "gx" ) )) # Int  |-> (point_x ((Znth 0 pts_l __default_Point))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.undef_full hull_pre n )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition graham_scan_safety_wit_14 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z)  __default_Point ,
  “ (pivot_idx = 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  ((( &( "gy" ) )) # Int  |-> (point_y ((Znth 0 pts_l __default_Point))))
  **  ((( &( "gx" ) )) # Int  |-> (point_x ((Znth 0 pts_l __default_Point))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.undef_full hull_pre n )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition graham_scan_safety_wit_15 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z)  __default_Point ,
  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (pivot_idx <> 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n (point_swap (pts_l) (0) (pivot_idx)) )
  **  ((( &( "gy" ) )) # Int  |-> (point_y ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point))))
  **  ((( &( "gx" ) )) # Int  |-> (point_x ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.undef_full hull_pre n )
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition graham_scan_safety_wit_16 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z)  __default_Point ,
  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (pivot_idx <> 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n (point_swap (pts_l) (0) (pivot_idx)) )
  **  ((( &( "gy" ) )) # Int  |-> (point_y ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point))))
  **  ((( &( "gx" ) )) # Int  |-> (point_x ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.undef_full hull_pre n )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition graham_scan_safety_wit_17 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z)  __default_Point ,
  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (pivot_idx <> 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n (point_swap (pts_l) (0) (pivot_idx)) )
  **  ((( &( "gy" ) )) # Int  |-> (point_y ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point))))
  **  ((( &( "gx" ) )) # Int  |-> (point_x ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.undef_full hull_pre n )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition graham_scan_safety_wit_18 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z) (pts_out: (@list Point))  __default_Point ,
  “ ((Zlength (pts_out)) = n) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation (point_swap (pts_l) (0) (pivot_idx)) pts_out ) ” 
  &&  “ (PointSameOutsideRange (point_swap (pts_l) (0) (pivot_idx)) pts_out 1 (n - 1 ) ) ” 
  &&  “ (PointSortedRange_Point (point_mk ((point_x ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point)))) ((point_y ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point))))) pts_out 1 (n - 1 ) ) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (pivot_idx <> 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((( &( "tail" ) )) # Ptr  |->_)
  **  (PointArray.full pts_pre n pts_out )
  **  ((( &( "gy" ) )) # Int  |-> (point_y ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point))))
  **  ((( &( "gx" ) )) # Int  |-> (point_x ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.undef_full hull_pre n )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition graham_scan_safety_wit_19 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z) (pts_out: (@list Point))  __default_Point ,
  “ ((Zlength (pts_out)) = n) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out 1 (n - 1 ) ) ” 
  &&  “ (PointSortedRange_Point (point_mk ((point_x ((Znth 0 pts_l __default_Point)))) ((point_y ((Znth 0 pts_l __default_Point))))) pts_out 1 (n - 1 ) ) ” 
  &&  “ (pivot_idx = 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((( &( "tail" ) )) # Ptr  |->_)
  **  (PointArray.full pts_pre n pts_out )
  **  ((( &( "gy" ) )) # Int  |-> (point_y ((Znth 0 pts_l __default_Point))))
  **  ((( &( "gx" ) )) # Int  |-> (point_x ((Znth 0 pts_l __default_Point))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.undef_full hull_pre n )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition graham_scan_safety_wit_20 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot: (@list Point)) (pts_sorted: (@list Point)) (tail_sorted: (@list Point)) (pivot0: Point) (tail: Z) (n: Z) (gy: Z) (gx: Z) (pivot_idx: Z)  __default_Point ,
  “ (tail = (pts_pre + sizeof( "Point" ) )) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < INT_MAX) ” 
  &&  “ (pivot0 = (point_mk (gx) (gy))) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_sorted)) = n) ” 
  &&  “ ((Zlength (tail_sorted)) = (n - 1 )) ” 
  &&  “ (tail_sorted = (sublist (1) (n) (pts_sorted))) ” 
  &&  “ (PointCoordsBound pts_sorted ) ” 
  &&  “ (PointCoordsBound tail_sorted ) ” 
  &&  “ (point_in_bound pivot0 ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (point_polar_sorted pivot0 tail_sorted ) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(y) ) = gy) ”
  &&  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "tail" ) )) # Ptr  |-> tail)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((&((pts_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pts_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full tail (n - 1 ) tail_sorted )
  **  (PointArray.undef_full hull_pre ((n - 1 ) + 1 ) )
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition graham_scan_safety_wit_21 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot: (@list Point)) (pts_sorted: (@list Point)) (tail_sorted: (@list Point)) (pivot0: Point) (tail: Z) (n: Z) (gy: Z) (gx: Z) (pivot_idx: Z)  __default_Point ,
  “ (tail = (pts_pre + sizeof( "Point" ) )) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < INT_MAX) ” 
  &&  “ (pivot0 = (point_mk (gx) (gy))) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_sorted)) = n) ” 
  &&  “ ((Zlength (tail_sorted)) = (n - 1 )) ” 
  &&  “ (tail_sorted = (sublist (1) (n) (pts_sorted))) ” 
  &&  “ (PointCoordsBound pts_sorted ) ” 
  &&  “ (PointCoordsBound tail_sorted ) ” 
  &&  “ (point_in_bound pivot0 ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (point_polar_sorted pivot0 tail_sorted ) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(y) ) = gy) ”
  &&  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "tail" ) )) # Ptr  |-> tail)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((&((pts_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pts_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full tail (n - 1 ) tail_sorted )
  **  (PointArray.undef_full hull_pre ((n - 1 ) + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition graham_scan_entail_wit_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n_pre pts_l )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < 1) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n_pre pts_l )
  **  (PointArray.undef_full hull_pre n_pre )
.

Definition graham_scan_entail_wit_2_1 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z) (retval: Z)  __default_Point ,
  “ (retval < 0) ” 
  &&  “ (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth i pts_l __default_Point)))) ((point_y ((Znth i pts_l __default_Point)))))) ((point_mk ((point_x ((Znth pivot_idx pts_l __default_Point)))) ((point_y ((Znth pivot_idx pts_l __default_Point)))))))) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (i + 1 )) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
.

Definition graham_scan_entail_wit_2_2 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z) (retval: Z)  __default_Point ,
  “ (retval >= 0) ” 
  &&  “ (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth i pts_l __default_Point)))) ((point_y ((Znth i pts_l __default_Point)))))) ((point_mk ((point_x ((Znth pivot_idx pts_l __default_Point)))) ((point_y ((Znth pivot_idx pts_l __default_Point)))))))) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < (i + 1 )) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
.

Definition graham_scan_entail_wit_3_1 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z) (pts_out: (@list Point))  __default_Point ,
  “ ((Zlength (pts_out)) = n) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation (point_swap (pts_l) (0) (pivot_idx)) pts_out ) ” 
  &&  “ (PointSameOutsideRange (point_swap (pts_l) (0) (pivot_idx)) pts_out 1 (n - 1 ) ) ” 
  &&  “ (PointSortedRange_Point (point_mk ((point_x ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point)))) ((point_y ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point))))) pts_out 1 (n - 1 ) ) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (pivot_idx <> 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_out )
  **  (PointArray.undef_full hull_pre n )
|--
  EX (tail_sorted: (@list Point))  (pts_sorted: (@list Point))  (pts_pivot: (@list Point))  (pivot0: Point) ,
  “ ((pts_pre + (1 * sizeof( "Point" ) ) ) = (pts_pre + sizeof( "Point" ) )) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < INT_MAX) ” 
  &&  “ (pivot0 = (point_mk ((point_x ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point)))) ((point_y ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point)))))) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_sorted)) = n) ” 
  &&  “ ((Zlength (tail_sorted)) = (n - 1 )) ” 
  &&  “ (tail_sorted = (sublist (1) (n) (pts_sorted))) ” 
  &&  “ (PointCoordsBound pts_sorted ) ” 
  &&  “ (PointCoordsBound tail_sorted ) ” 
  &&  “ (point_in_bound pivot0 ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSortedRange_Point (point_mk ((point_x ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point)))) ((point_y ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point))))) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (point_polar_sorted pivot0 tail_sorted ) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(x) ) = (point_x ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point)))) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(y) ) = (point_y ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point)))) ”
  &&  ((&((pts_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pts_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full (pts_pre + (1 * sizeof( "Point" ) ) ) (n - 1 ) tail_sorted )
  **  (PointArray.undef_full hull_pre ((n - 1 ) + 1 ) )
.

Definition graham_scan_entail_wit_3_2 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z) (pts_out: (@list Point))  __default_Point ,
  “ ((Zlength (pts_out)) = n) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out 1 (n - 1 ) ) ” 
  &&  “ (PointSortedRange_Point (point_mk ((point_x ((Znth 0 pts_l __default_Point)))) ((point_y ((Znth 0 pts_l __default_Point))))) pts_out 1 (n - 1 ) ) ” 
  &&  “ (pivot_idx = 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_out )
  **  (PointArray.undef_full hull_pre n )
|--
  EX (tail_sorted: (@list Point))  (pts_sorted: (@list Point))  (pts_pivot: (@list Point))  (pivot0: Point) ,
  “ ((pts_pre + (1 * sizeof( "Point" ) ) ) = (pts_pre + sizeof( "Point" ) )) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < INT_MAX) ” 
  &&  “ (pivot0 = (point_mk ((point_x ((Znth 0 pts_l __default_Point)))) ((point_y ((Znth 0 pts_l __default_Point)))))) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_sorted)) = n) ” 
  &&  “ ((Zlength (tail_sorted)) = (n - 1 )) ” 
  &&  “ (tail_sorted = (sublist (1) (n) (pts_sorted))) ” 
  &&  “ (PointCoordsBound pts_sorted ) ” 
  &&  “ (PointCoordsBound tail_sorted ) ” 
  &&  “ (point_in_bound pivot0 ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSortedRange_Point (point_mk ((point_x ((Znth 0 pts_l __default_Point)))) ((point_y ((Znth 0 pts_l __default_Point))))) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (point_polar_sorted pivot0 tail_sorted ) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(x) ) = (point_x ((Znth 0 pts_l __default_Point)))) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(y) ) = (point_y ((Znth 0 pts_l __default_Point)))) ”
  &&  ((&((pts_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pts_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full (pts_pre + (1 * sizeof( "Point" ) ) ) (n - 1 ) tail_sorted )
  **  (PointArray.undef_full hull_pre ((n - 1 ) + 1 ) )
.

Definition graham_scan_return_wit_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot: (@list Point)) (pts_sorted: (@list Point)) (tail_sorted: (@list Point)) (pivot0: Point) (tail: Z) (n: Z) (gy: Z) (gx: Z) (pivot_idx: Z) (hull_out_2: (@list Point)) (retval: Z)  __default_Point ,
  “ (retval = (Zlength (hull_out_2))) ” 
  &&  “ (point_in_bound pivot0 ) ” 
  &&  “ (PointCoordsBound tail_sorted ) ” 
  &&  “ (is_convex_hull tail_sorted hull_out_2 ) ” 
  &&  “ (tail = (pts_pre + sizeof( "Point" ) )) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < INT_MAX) ” 
  &&  “ (pivot0 = (point_mk (gx) (gy))) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_sorted)) = n) ” 
  &&  “ ((Zlength (tail_sorted)) = (n - 1 )) ” 
  &&  “ (tail_sorted = (sublist (1) (n) (pts_sorted))) ” 
  &&  “ (PointCoordsBound pts_sorted ) ” 
  &&  “ (PointCoordsBound tail_sorted ) ” 
  &&  “ (point_in_bound pivot0 ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (point_polar_sorted pivot0 tail_sorted ) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(y) ) = gy) ”
  &&  ((&((pts_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pts_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full tail (n - 1 ) tail_sorted )
  **  (PointArray.seg hull_pre 0 retval hull_out_2 )
  **  (PointArray.undef_seg hull_pre retval ((n - 1 ) + 1 ) )
|--
  EX (hull_out: (@list Point))  (pts_out: (@list Point)) ,
  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ ((Zlength (hull_out)) <= n_pre) ” 
  &&  “ ((Zlength (hull_out)) >= 1) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (is_convex_hull pts_l hull_out ) ” 
  &&  “ (retval = (Zlength (hull_out))) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
  **  (PointArray.seg hull_pre 0 retval hull_out )
  **  (PointArray.undef_seg hull_pre retval n_pre )
.

Definition graham_scan_partial_solve_wit_1 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z)  __default_Point ,
  “ (i < n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (i < n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((&(((pts_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_l __default_Point))))
  **  (PointArray.missing_i pts_pre i 0 n pts_l )
  **  ((&(((pts_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_l __default_Point))))
  **  (PointArray.undef_full hull_pre n )
.

Definition graham_scan_partial_solve_wit_2 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z)  __default_Point ,
  “ (i < n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (i < n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((&(((pts_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_l __default_Point))))
  **  (PointArray.missing_i pts_pre i 0 n pts_l )
  **  ((&(((pts_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_l __default_Point))))
  **  (PointArray.undef_full hull_pre n )
.

Definition graham_scan_partial_solve_wit_3 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z)  __default_Point ,
  “ (i < n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (i < n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((&(((pts_pre + (pivot_idx * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth pivot_idx pts_l __default_Point))))
  **  (PointArray.missing_i pts_pre pivot_idx 0 n pts_l )
  **  ((&(((pts_pre + (pivot_idx * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth pivot_idx pts_l __default_Point))))
  **  (PointArray.undef_full hull_pre n )
.

Definition graham_scan_partial_solve_wit_4 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z)  __default_Point ,
  “ (i < n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (i < n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((&(((pts_pre + (pivot_idx * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth pivot_idx pts_l __default_Point))))
  **  (PointArray.missing_i pts_pre pivot_idx 0 n pts_l )
  **  ((&(((pts_pre + (pivot_idx * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth pivot_idx pts_l __default_Point))))
  **  (PointArray.undef_full hull_pre n )
.

Definition graham_scan_partial_solve_wit_5 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z) ,
  “ (i < n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (i < n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
.

Definition graham_scan_partial_solve_wit_6_pure := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z) ,
  “ (pivot_idx <> 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= 0) ” 
  &&  “ (0 < n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ (0 <> pivot_idx) ” 
  &&  “ ((Zlength (pts_l)) = n) ”
.

Definition graham_scan_partial_solve_wit_6_aux := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z) ,
  “ (pivot_idx <> 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= 0) ” 
  &&  “ (0 < n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ (0 <> pivot_idx) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (pivot_idx <> 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
.

Definition graham_scan_partial_solve_wit_6 := graham_scan_partial_solve_wit_6_pure -> graham_scan_partial_solve_wit_6_aux.

Definition graham_scan_partial_solve_wit_7 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z)  __default_Point ,
  “ (pivot_idx = 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (pivot_idx = 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((&(((pts_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth 0 pts_l __default_Point))))
  **  (PointArray.missing_i pts_pre 0 0 n pts_l )
  **  ((&(((pts_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth 0 pts_l __default_Point))))
  **  (PointArray.undef_full hull_pre n )
.

Definition graham_scan_partial_solve_wit_8 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z)  __default_Point ,
  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (pivot_idx <> 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n (point_swap (pts_l) (0) (pivot_idx)) )
  **  (PointArray.undef_full hull_pre n )
|--
  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (pivot_idx <> 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((&(((pts_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point))))
  **  (PointArray.missing_i pts_pre 0 0 n (point_swap (pts_l) (0) (pivot_idx)) )
  **  ((&(((pts_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point))))
  **  (PointArray.undef_full hull_pre n )
.

Definition graham_scan_partial_solve_wit_9 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z)  __default_Point ,
  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (pivot_idx <> 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n (point_swap (pts_l) (0) (pivot_idx)) )
  **  (PointArray.undef_full hull_pre n )
|--
  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (pivot_idx <> 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((&(((pts_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point))))
  **  (PointArray.missing_i pts_pre 0 0 n (point_swap (pts_l) (0) (pivot_idx)) )
  **  ((&(((pts_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point))))
  **  (PointArray.undef_full hull_pre n )
.

Definition graham_scan_partial_solve_wit_10 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z)  __default_Point ,
  “ (pivot_idx = 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (pivot_idx = 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((&(((pts_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth 0 pts_l __default_Point))))
  **  (PointArray.missing_i pts_pre 0 0 n pts_l )
  **  ((&(((pts_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth 0 pts_l __default_Point))))
  **  (PointArray.undef_full hull_pre n )
.

Definition graham_scan_partial_solve_wit_11_pure := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z)  __default_Point ,
  “ (pivot_idx = 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  ((( &( "gy" ) )) # Int  |-> (point_y ((Znth 0 pts_l __default_Point))))
  **  ((( &( "gx" ) )) # Int  |-> (point_x ((Znth 0 pts_l __default_Point))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((-1) <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < n) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk ((point_x ((Znth 0 pts_l __default_Point)))) ((point_y ((Znth 0 pts_l __default_Point))))) ) ”
.

Definition graham_scan_partial_solve_wit_11_aux := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z)  __default_Point ,
  “ (pivot_idx = 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((-1) <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < n) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk ((point_x ((Znth 0 pts_l __default_Point)))) ((point_y ((Znth 0 pts_l __default_Point))))) ) ” 
  &&  “ (pivot_idx = 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
.

Definition graham_scan_partial_solve_wit_11 := graham_scan_partial_solve_wit_11_pure -> graham_scan_partial_solve_wit_11_aux.

Definition graham_scan_partial_solve_wit_12_pure := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z)  __default_Point ,
  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (pivot_idx <> 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n (point_swap (pts_l) (0) (pivot_idx)) )
  **  ((( &( "gy" ) )) # Int  |-> (point_y ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point))))
  **  ((( &( "gx" ) )) # Int  |-> (point_x ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((-1) <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < n) ” 
  &&  “ (point_in_bound (point_mk ((point_x ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point)))) ((point_y ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point))))) ) ” 
  &&  “ (PointCoordsBound (point_swap (pts_l) (0) (pivot_idx)) ) ” 
  &&  “ ((Zlength ((point_swap (pts_l) (0) (pivot_idx)))) = n) ”
.

Definition graham_scan_partial_solve_wit_12_aux := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_idx: Z) (i: Z) (n: Z)  __default_Point ,
  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (pivot_idx <> 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n (point_swap (pts_l) (0) (pivot_idx)) )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((-1) <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < n) ” 
  &&  “ (point_in_bound (point_mk ((point_x ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point)))) ((point_y ((Znth 0 (point_swap (pts_l) (0) (pivot_idx)) __default_Point))))) ) ” 
  &&  “ (PointCoordsBound (point_swap (pts_l) (0) (pivot_idx)) ) ” 
  &&  “ ((Zlength ((point_swap (pts_l) (0) (pivot_idx)))) = n) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (pivot_idx <> 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (PointArray.full pts_pre n (point_swap (pts_l) (0) (pivot_idx)) )
  **  (PointArray.undef_full hull_pre n )
.

Definition graham_scan_partial_solve_wit_12 := graham_scan_partial_solve_wit_12_pure -> graham_scan_partial_solve_wit_12_aux.

Definition graham_scan_partial_solve_wit_13_pure := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot: (@list Point)) (pts_sorted: (@list Point)) (tail_sorted: (@list Point)) (pivot0: Point) (tail: Z) (n: Z) (gy: Z) (gx: Z) (pivot_idx: Z)  __default_Point ,
  “ (tail = (pts_pre + sizeof( "Point" ) )) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < INT_MAX) ” 
  &&  “ (pivot0 = (point_mk (gx) (gy))) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_sorted)) = n) ” 
  &&  “ ((Zlength (tail_sorted)) = (n - 1 )) ” 
  &&  “ (tail_sorted = (sublist (1) (n) (pts_sorted))) ” 
  &&  “ (PointCoordsBound pts_sorted ) ” 
  &&  “ (PointCoordsBound tail_sorted ) ” 
  &&  “ (point_in_bound pivot0 ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (point_polar_sorted pivot0 tail_sorted ) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(y) ) = gy) ”
  &&  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "tail" ) )) # Ptr  |-> tail)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((&((pts_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pts_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full tail (n - 1 ) tail_sorted )
  **  (PointArray.undef_full hull_pre ((n - 1 ) + 1 ) )
|--
  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < INT_MAX) ” 
  &&  “ ((n - 1 ) = (Zlength (tail_sorted))) ” 
  &&  “ (point_polar_sorted pivot0 tail_sorted ) ” 
  &&  “ (point_in_bound pivot0 ) ” 
  &&  “ (PointCoordsBound tail_sorted ) ” 
  &&  “ (((Zlength (pts_sorted)) - 1 ) = (Zlength ((sublist (1) (n) (pts_sorted))))) ”
.

Definition graham_scan_partial_solve_wit_13_aux := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot: (@list Point)) (pts_sorted: (@list Point)) (tail_sorted: (@list Point)) (pivot0: Point) (tail: Z) (n: Z) (gy: Z) (gx: Z) (pivot_idx: Z)  __default_Point ,
  “ (tail = (pts_pre + sizeof( "Point" ) )) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < INT_MAX) ” 
  &&  “ (pivot0 = (point_mk (gx) (gy))) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_sorted)) = n) ” 
  &&  “ ((Zlength (tail_sorted)) = (n - 1 )) ” 
  &&  “ (tail_sorted = (sublist (1) (n) (pts_sorted))) ” 
  &&  “ (PointCoordsBound pts_sorted ) ” 
  &&  “ (PointCoordsBound tail_sorted ) ” 
  &&  “ (point_in_bound pivot0 ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (point_polar_sorted pivot0 tail_sorted ) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(y) ) = gy) ”
  &&  ((&((pts_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pts_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full tail (n - 1 ) tail_sorted )
  **  (PointArray.undef_full hull_pre ((n - 1 ) + 1 ) )
|--
  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < INT_MAX) ” 
  &&  “ ((n - 1 ) = (Zlength (tail_sorted))) ” 
  &&  “ (point_polar_sorted pivot0 tail_sorted ) ” 
  &&  “ (point_in_bound pivot0 ) ” 
  &&  “ (PointCoordsBound tail_sorted ) ” 
  &&  “ (((Zlength (pts_sorted)) - 1 ) = (Zlength ((sublist (1) (n) (pts_sorted))))) ” 
  &&  “ (tail = (pts_pre + sizeof( "Point" ) )) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < INT_MAX) ” 
  &&  “ (pivot0 = (point_mk (gx) (gy))) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_sorted)) = n) ” 
  &&  “ ((Zlength (tail_sorted)) = (n - 1 )) ” 
  &&  “ (tail_sorted = (sublist (1) (n) (pts_sorted))) ” 
  &&  “ (PointCoordsBound pts_sorted ) ” 
  &&  “ (PointCoordsBound tail_sorted ) ” 
  &&  “ (point_in_bound pivot0 ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (point_polar_sorted pivot0 tail_sorted ) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(y) ) = gy) ”
  &&  ((&((pts_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pts_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full tail (n - 1 ) tail_sorted )
  **  (PointArray.undef_full hull_pre ((n - 1 ) + 1 ) )
.

Definition graham_scan_partial_solve_wit_13 := graham_scan_partial_solve_wit_13_pure -> graham_scan_partial_solve_wit_13_aux.

Definition build_hull_from_sorted_tail_derive_high_level_spec_by_low_level_spec := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (l_high_level_spec: (@list Point)) (pivot0_high_level_spec: Point) ,
  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_high_level_spec))) ” 
  &&  “ (point_polar_sorted pivot0_high_level_spec l_high_level_spec ) ” 
  &&  “ (point_in_bound pivot0_high_level_spec ) ” 
  &&  “ (PointCoordsBound l_high_level_spec ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_high_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_high_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_high_level_spec )
  **  (PointArray.undef_full hull_pre (tail_n_pre + 1 ) )
|--
EX (pivot0_low_level_spec: Point) (l_low_level_spec: (@list Point)) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) ,
  (“ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (safeExec (equiv (empty_point_stack)) (build_hull (pivot0_low_level_spec) (l_low_level_spec)) X_low_level_spec ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_full hull_pre (tail_n_pre + 1 ) ))
  **
  ((EX stk retval_2,
  “ (retval_2 = (Zlength ((rev (stk))))) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (PointCoordsBound l_low_level_spec ) ” 
  &&  “ (PointCoordsBound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (return (tt)) X_low_level_spec ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_low_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_low_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 retval_2 (rev (stk)) )
  **  (PointArray.undef_seg hull_pre retval_2 (tail_n_pre + 1 ) ))
  -*
  (EX hull_out retval,
  “ (retval = (Zlength (hull_out))) ” 
  &&  “ (point_in_bound pivot0_high_level_spec ) ” 
  &&  “ (PointCoordsBound l_high_level_spec ) ” 
  &&  “ (is_convex_hull l_high_level_spec hull_out ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0_high_level_spec.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0_high_level_spec.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_high_level_spec )
  **  (PointArray.seg hull_pre 0 retval hull_out )
  **  (PointArray.undef_seg hull_pre retval (tail_n_pre + 1 ) )))
.

Module Type VC_Correct.

Include point_array_Strategy_Correct.
Include safeexec_Strategy_Correct.

Axiom proof_of_leftdown_safety_wit_1 : leftdown_safety_wit_1.
Axiom proof_of_leftdown_safety_wit_2 : leftdown_safety_wit_2.
Axiom proof_of_leftdown_safety_wit_3 : leftdown_safety_wit_3.
Axiom proof_of_leftdown_safety_wit_4 : leftdown_safety_wit_4.
Axiom proof_of_leftdown_safety_wit_5 : leftdown_safety_wit_5.
Axiom proof_of_leftdown_safety_wit_6 : leftdown_safety_wit_6.
Axiom proof_of_leftdown_safety_wit_7 : leftdown_safety_wit_7.
Axiom proof_of_leftdown_entail_wit_1 : leftdown_entail_wit_1.
Axiom proof_of_leftdown_return_wit_1 : leftdown_return_wit_1.
Axiom proof_of_leftdown_return_wit_2 : leftdown_return_wit_2.
Axiom proof_of_leftdown_return_wit_3 : leftdown_return_wit_3.
Axiom proof_of_leftdown_return_wit_4 : leftdown_return_wit_4.
Axiom proof_of_leftdown_return_wit_5 : leftdown_return_wit_5.
Axiom proof_of_cross_prod_safety_wit_1 : cross_prod_safety_wit_1.
Axiom proof_of_cross_prod_safety_wit_2 : cross_prod_safety_wit_2.
Axiom proof_of_cross_prod_safety_wit_3 : cross_prod_safety_wit_3.
Axiom proof_of_cross_prod_safety_wit_4 : cross_prod_safety_wit_4.
Axiom proof_of_cross_prod_safety_wit_5 : cross_prod_safety_wit_5.
Axiom proof_of_cross_prod_safety_wit_6 : cross_prod_safety_wit_6.
Axiom proof_of_cross_prod_safety_wit_7 : cross_prod_safety_wit_7.
Axiom proof_of_cross_prod_entail_wit_1 : cross_prod_entail_wit_1.
Axiom proof_of_cross_prod_return_wit_1 : cross_prod_return_wit_1.
Axiom proof_of_dot_prod_safety_wit_1 : dot_prod_safety_wit_1.
Axiom proof_of_dot_prod_safety_wit_2 : dot_prod_safety_wit_2.
Axiom proof_of_dot_prod_safety_wit_3 : dot_prod_safety_wit_3.
Axiom proof_of_dot_prod_safety_wit_4 : dot_prod_safety_wit_4.
Axiom proof_of_dot_prod_safety_wit_5 : dot_prod_safety_wit_5.
Axiom proof_of_dot_prod_safety_wit_6 : dot_prod_safety_wit_6.
Axiom proof_of_dot_prod_safety_wit_7 : dot_prod_safety_wit_7.
Axiom proof_of_dot_prod_entail_wit_1 : dot_prod_entail_wit_1.
Axiom proof_of_dot_prod_return_wit_1 : dot_prod_return_wit_1.
Axiom proof_of_cmp_polar_safety_wit_1 : cmp_polar_safety_wit_1.
Axiom proof_of_cmp_polar_safety_wit_2 : cmp_polar_safety_wit_2.
Axiom proof_of_cmp_polar_safety_wit_3 : cmp_polar_safety_wit_3.
Axiom proof_of_cmp_polar_safety_wit_4 : cmp_polar_safety_wit_4.
Axiom proof_of_cmp_polar_safety_wit_5 : cmp_polar_safety_wit_5.
Axiom proof_of_cmp_polar_safety_wit_6 : cmp_polar_safety_wit_6.
Axiom proof_of_cmp_polar_safety_wit_7 : cmp_polar_safety_wit_7.
Axiom proof_of_cmp_polar_safety_wit_8 : cmp_polar_safety_wit_8.
Axiom proof_of_cmp_polar_safety_wit_9 : cmp_polar_safety_wit_9.
Axiom proof_of_cmp_polar_safety_wit_10 : cmp_polar_safety_wit_10.
Axiom proof_of_cmp_polar_safety_wit_11 : cmp_polar_safety_wit_11.
Axiom proof_of_cmp_polar_safety_wit_12 : cmp_polar_safety_wit_12.
Axiom proof_of_cmp_polar_safety_wit_13 : cmp_polar_safety_wit_13.
Axiom proof_of_cmp_polar_safety_wit_14 : cmp_polar_safety_wit_14.
Axiom proof_of_cmp_polar_safety_wit_15 : cmp_polar_safety_wit_15.
Axiom proof_of_cmp_polar_safety_wit_16 : cmp_polar_safety_wit_16.
Axiom proof_of_cmp_polar_safety_wit_17 : cmp_polar_safety_wit_17.
Axiom proof_of_cmp_polar_safety_wit_18 : cmp_polar_safety_wit_18.
Axiom proof_of_cmp_polar_safety_wit_19 : cmp_polar_safety_wit_19.
Axiom proof_of_cmp_polar_safety_wit_20 : cmp_polar_safety_wit_20.
Axiom proof_of_cmp_polar_safety_wit_21 : cmp_polar_safety_wit_21.
Axiom proof_of_cmp_polar_safety_wit_22 : cmp_polar_safety_wit_22.
Axiom proof_of_cmp_polar_safety_wit_23 : cmp_polar_safety_wit_23.
Axiom proof_of_cmp_polar_safety_wit_24 : cmp_polar_safety_wit_24.
Axiom proof_of_cmp_polar_entail_wit_1 : cmp_polar_entail_wit_1.
Axiom proof_of_cmp_polar_entail_wit_2 : cmp_polar_entail_wit_2.
Axiom proof_of_cmp_polar_entail_wit_3 : cmp_polar_entail_wit_3.
Axiom proof_of_cmp_polar_return_wit_1 : cmp_polar_return_wit_1.
Axiom proof_of_cmp_polar_return_wit_2 : cmp_polar_return_wit_2.
Axiom proof_of_cmp_polar_return_wit_3 : cmp_polar_return_wit_3.
Axiom proof_of_cmp_polar_return_wit_4 : cmp_polar_return_wit_4.
Axiom proof_of_cmp_polar_return_wit_5 : cmp_polar_return_wit_5.
Axiom proof_of_cmp_polar_return_wit_6 : cmp_polar_return_wit_6.
Axiom proof_of_cmp_polar_return_wit_7 : cmp_polar_return_wit_7.
Axiom proof_of_cmp_polar_return_wit_8 : cmp_polar_return_wit_8.
Axiom proof_of_cmp_polar_return_wit_9 : cmp_polar_return_wit_9.
Axiom proof_of_cmp_polar_partial_solve_wit_1_pure : cmp_polar_partial_solve_wit_1_pure.
Axiom proof_of_cmp_polar_partial_solve_wit_1 : cmp_polar_partial_solve_wit_1.
Axiom proof_of_build_hull_from_sorted_tail_safety_wit_1 : build_hull_from_sorted_tail_safety_wit_1.
Axiom proof_of_build_hull_from_sorted_tail_safety_wit_2 : build_hull_from_sorted_tail_safety_wit_2.
Axiom proof_of_build_hull_from_sorted_tail_safety_wit_3 : build_hull_from_sorted_tail_safety_wit_3.
Axiom proof_of_build_hull_from_sorted_tail_safety_wit_4 : build_hull_from_sorted_tail_safety_wit_4.
Axiom proof_of_build_hull_from_sorted_tail_safety_wit_5 : build_hull_from_sorted_tail_safety_wit_5.
Axiom proof_of_build_hull_from_sorted_tail_safety_wit_6 : build_hull_from_sorted_tail_safety_wit_6.
Axiom proof_of_build_hull_from_sorted_tail_safety_wit_7 : build_hull_from_sorted_tail_safety_wit_7.
Axiom proof_of_build_hull_from_sorted_tail_safety_wit_8 : build_hull_from_sorted_tail_safety_wit_8.
Axiom proof_of_build_hull_from_sorted_tail_safety_wit_9 : build_hull_from_sorted_tail_safety_wit_9.
Axiom proof_of_build_hull_from_sorted_tail_safety_wit_10 : build_hull_from_sorted_tail_safety_wit_10.
Axiom proof_of_build_hull_from_sorted_tail_safety_wit_11 : build_hull_from_sorted_tail_safety_wit_11.
Axiom proof_of_build_hull_from_sorted_tail_safety_wit_12 : build_hull_from_sorted_tail_safety_wit_12.
Axiom proof_of_build_hull_from_sorted_tail_safety_wit_13 : build_hull_from_sorted_tail_safety_wit_13.
Axiom proof_of_build_hull_from_sorted_tail_safety_wit_14 : build_hull_from_sorted_tail_safety_wit_14.
Axiom proof_of_build_hull_from_sorted_tail_safety_wit_15 : build_hull_from_sorted_tail_safety_wit_15.
Axiom proof_of_build_hull_from_sorted_tail_safety_wit_16 : build_hull_from_sorted_tail_safety_wit_16.
Axiom proof_of_build_hull_from_sorted_tail_safety_wit_17 : build_hull_from_sorted_tail_safety_wit_17.
Axiom proof_of_build_hull_from_sorted_tail_safety_wit_18 : build_hull_from_sorted_tail_safety_wit_18.
Axiom proof_of_build_hull_from_sorted_tail_safety_wit_19 : build_hull_from_sorted_tail_safety_wit_19.
Axiom proof_of_build_hull_from_sorted_tail_entail_wit_1 : build_hull_from_sorted_tail_entail_wit_1.
Axiom proof_of_build_hull_from_sorted_tail_entail_wit_2 : build_hull_from_sorted_tail_entail_wit_2.
Axiom proof_of_build_hull_from_sorted_tail_entail_wit_3 : build_hull_from_sorted_tail_entail_wit_3.
Axiom proof_of_build_hull_from_sorted_tail_entail_wit_4_1 : build_hull_from_sorted_tail_entail_wit_4_1.
Axiom proof_of_build_hull_from_sorted_tail_entail_wit_4_2 : build_hull_from_sorted_tail_entail_wit_4_2.
Axiom proof_of_build_hull_from_sorted_tail_return_wit_1 : build_hull_from_sorted_tail_return_wit_1.
Axiom proof_of_build_hull_from_sorted_tail_partial_solve_wit_1 : build_hull_from_sorted_tail_partial_solve_wit_1.
Axiom proof_of_build_hull_from_sorted_tail_partial_solve_wit_2 : build_hull_from_sorted_tail_partial_solve_wit_2.
Axiom proof_of_build_hull_from_sorted_tail_partial_solve_wit_3 : build_hull_from_sorted_tail_partial_solve_wit_3.
Axiom proof_of_build_hull_from_sorted_tail_partial_solve_wit_4 : build_hull_from_sorted_tail_partial_solve_wit_4.
Axiom proof_of_build_hull_from_sorted_tail_partial_solve_wit_5 : build_hull_from_sorted_tail_partial_solve_wit_5.
Axiom proof_of_build_hull_from_sorted_tail_partial_solve_wit_6 : build_hull_from_sorted_tail_partial_solve_wit_6.
Axiom proof_of_build_hull_from_sorted_tail_partial_solve_wit_7 : build_hull_from_sorted_tail_partial_solve_wit_7.
Axiom proof_of_build_hull_from_sorted_tail_partial_solve_wit_8_pure : build_hull_from_sorted_tail_partial_solve_wit_8_pure.
Axiom proof_of_build_hull_from_sorted_tail_partial_solve_wit_8 : build_hull_from_sorted_tail_partial_solve_wit_8.
Axiom proof_of_build_hull_from_sorted_tail_partial_solve_wit_9 : build_hull_from_sorted_tail_partial_solve_wit_9.
Axiom proof_of_build_hull_from_sorted_tail_partial_solve_wit_10 : build_hull_from_sorted_tail_partial_solve_wit_10.
Axiom proof_of_build_hull_from_sorted_tail_partial_solve_wit_11 : build_hull_from_sorted_tail_partial_solve_wit_11.
Axiom proof_of_build_hull_from_sorted_tail_partial_solve_wit_12 : build_hull_from_sorted_tail_partial_solve_wit_12.
Axiom proof_of_build_hull_from_sorted_tail_partial_solve_wit_13 : build_hull_from_sorted_tail_partial_solve_wit_13.
Axiom proof_of_build_hull_from_sorted_tail_partial_solve_wit_14 : build_hull_from_sorted_tail_partial_solve_wit_14.
Axiom proof_of_swap_points_entail_wit_1 : swap_points_entail_wit_1.
Axiom proof_of_swap_points_entail_wit_2 : swap_points_entail_wit_2.
Axiom proof_of_swap_points_return_wit_1 : swap_points_return_wit_1.
Axiom proof_of_swap_points_return_wit_2 : swap_points_return_wit_2.
Axiom proof_of_partition_polar_points_safety_wit_1 : partition_polar_points_safety_wit_1.
Axiom proof_of_partition_polar_points_safety_wit_2 : partition_polar_points_safety_wit_2.
Axiom proof_of_partition_polar_points_safety_wit_3 : partition_polar_points_safety_wit_3.
Axiom proof_of_partition_polar_points_safety_wit_4 : partition_polar_points_safety_wit_4.
Axiom proof_of_partition_polar_points_safety_wit_5 : partition_polar_points_safety_wit_5.
Axiom proof_of_partition_polar_points_safety_wit_6 : partition_polar_points_safety_wit_6.
Axiom proof_of_partition_polar_points_safety_wit_7 : partition_polar_points_safety_wit_7.
Axiom proof_of_partition_polar_points_safety_wit_8 : partition_polar_points_safety_wit_8.
Axiom proof_of_partition_polar_points_safety_wit_9 : partition_polar_points_safety_wit_9.
Axiom proof_of_partition_polar_points_safety_wit_10 : partition_polar_points_safety_wit_10.
Axiom proof_of_partition_polar_points_safety_wit_11 : partition_polar_points_safety_wit_11.
Axiom proof_of_partition_polar_points_safety_wit_12 : partition_polar_points_safety_wit_12.
Axiom proof_of_partition_polar_points_safety_wit_13 : partition_polar_points_safety_wit_13.
Axiom proof_of_partition_polar_points_safety_wit_14 : partition_polar_points_safety_wit_14.
Axiom proof_of_partition_polar_points_safety_wit_15 : partition_polar_points_safety_wit_15.
Axiom proof_of_partition_polar_points_entail_wit_1 : partition_polar_points_entail_wit_1.
Axiom proof_of_partition_polar_points_entail_wit_2 : partition_polar_points_entail_wit_2.
Axiom proof_of_partition_polar_points_entail_wit_3 : partition_polar_points_entail_wit_3.
Axiom proof_of_partition_polar_points_entail_wit_4 : partition_polar_points_entail_wit_4.
Axiom proof_of_partition_polar_points_entail_wit_5_1 : partition_polar_points_entail_wit_5_1.
Axiom proof_of_partition_polar_points_entail_wit_5_2 : partition_polar_points_entail_wit_5_2.
Axiom proof_of_partition_polar_points_entail_wit_5_3 : partition_polar_points_entail_wit_5_3.
Axiom proof_of_partition_polar_points_return_wit_1 : partition_polar_points_return_wit_1.
Axiom proof_of_partition_polar_points_return_wit_2 : partition_polar_points_return_wit_2.
Axiom proof_of_partition_polar_points_partial_solve_wit_1_pure : partition_polar_points_partial_solve_wit_1_pure.
Axiom proof_of_partition_polar_points_partial_solve_wit_1 : partition_polar_points_partial_solve_wit_1.
Axiom proof_of_partition_polar_points_partial_solve_wit_2_pure : partition_polar_points_partial_solve_wit_2_pure.
Axiom proof_of_partition_polar_points_partial_solve_wit_2 : partition_polar_points_partial_solve_wit_2.
Axiom proof_of_partition_polar_points_partial_solve_wit_3_pure : partition_polar_points_partial_solve_wit_3_pure.
Axiom proof_of_partition_polar_points_partial_solve_wit_3 : partition_polar_points_partial_solve_wit_3.
Axiom proof_of_quicksort_polar_points_safety_wit_1 : quicksort_polar_points_safety_wit_1.
Axiom proof_of_quicksort_polar_points_safety_wit_2 : quicksort_polar_points_safety_wit_2.
Axiom proof_of_quicksort_polar_points_safety_wit_3 : quicksort_polar_points_safety_wit_3.
Axiom proof_of_quicksort_polar_points_safety_wit_4 : quicksort_polar_points_safety_wit_4.
Axiom proof_of_quicksort_polar_points_safety_wit_5 : quicksort_polar_points_safety_wit_5.
Axiom proof_of_quicksort_polar_points_safety_wit_6 : quicksort_polar_points_safety_wit_6.
Axiom proof_of_quicksort_polar_points_safety_wit_7 : quicksort_polar_points_safety_wit_7.
Axiom proof_of_quicksort_polar_points_return_wit_1 : quicksort_polar_points_return_wit_1.
Axiom proof_of_quicksort_polar_points_return_wit_2 : quicksort_polar_points_return_wit_2.
Axiom proof_of_quicksort_polar_points_return_wit_3 : quicksort_polar_points_return_wit_3.
Axiom proof_of_quicksort_polar_points_return_wit_4 : quicksort_polar_points_return_wit_4.
Axiom proof_of_quicksort_polar_points_partial_solve_wit_1_pure : quicksort_polar_points_partial_solve_wit_1_pure.
Axiom proof_of_quicksort_polar_points_partial_solve_wit_1 : quicksort_polar_points_partial_solve_wit_1.
Axiom proof_of_quicksort_polar_points_partial_solve_wit_2_pure : quicksort_polar_points_partial_solve_wit_2_pure.
Axiom proof_of_quicksort_polar_points_partial_solve_wit_2 : quicksort_polar_points_partial_solve_wit_2.
Axiom proof_of_quicksort_polar_points_partial_solve_wit_3_pure : quicksort_polar_points_partial_solve_wit_3_pure.
Axiom proof_of_quicksort_polar_points_partial_solve_wit_3 : quicksort_polar_points_partial_solve_wit_3.
Axiom proof_of_quicksort_polar_points_partial_solve_wit_4_pure : quicksort_polar_points_partial_solve_wit_4_pure.
Axiom proof_of_quicksort_polar_points_partial_solve_wit_4 : quicksort_polar_points_partial_solve_wit_4.
Axiom proof_of_graham_scan_safety_wit_1 : graham_scan_safety_wit_1.
Axiom proof_of_graham_scan_safety_wit_2 : graham_scan_safety_wit_2.
Axiom proof_of_graham_scan_safety_wit_3 : graham_scan_safety_wit_3.
Axiom proof_of_graham_scan_safety_wit_4 : graham_scan_safety_wit_4.
Axiom proof_of_graham_scan_safety_wit_5 : graham_scan_safety_wit_5.
Axiom proof_of_graham_scan_safety_wit_6 : graham_scan_safety_wit_6.
Axiom proof_of_graham_scan_safety_wit_7 : graham_scan_safety_wit_7.
Axiom proof_of_graham_scan_safety_wit_8 : graham_scan_safety_wit_8.
Axiom proof_of_graham_scan_safety_wit_9 : graham_scan_safety_wit_9.
Axiom proof_of_graham_scan_safety_wit_10 : graham_scan_safety_wit_10.
Axiom proof_of_graham_scan_safety_wit_11 : graham_scan_safety_wit_11.
Axiom proof_of_graham_scan_safety_wit_12 : graham_scan_safety_wit_12.
Axiom proof_of_graham_scan_safety_wit_13 : graham_scan_safety_wit_13.
Axiom proof_of_graham_scan_safety_wit_14 : graham_scan_safety_wit_14.
Axiom proof_of_graham_scan_safety_wit_15 : graham_scan_safety_wit_15.
Axiom proof_of_graham_scan_safety_wit_16 : graham_scan_safety_wit_16.
Axiom proof_of_graham_scan_safety_wit_17 : graham_scan_safety_wit_17.
Axiom proof_of_graham_scan_safety_wit_18 : graham_scan_safety_wit_18.
Axiom proof_of_graham_scan_safety_wit_19 : graham_scan_safety_wit_19.
Axiom proof_of_graham_scan_safety_wit_20 : graham_scan_safety_wit_20.
Axiom proof_of_graham_scan_safety_wit_21 : graham_scan_safety_wit_21.
Axiom proof_of_graham_scan_entail_wit_1 : graham_scan_entail_wit_1.
Axiom proof_of_graham_scan_entail_wit_2_1 : graham_scan_entail_wit_2_1.
Axiom proof_of_graham_scan_entail_wit_2_2 : graham_scan_entail_wit_2_2.
Axiom proof_of_graham_scan_entail_wit_3_1 : graham_scan_entail_wit_3_1.
Axiom proof_of_graham_scan_entail_wit_3_2 : graham_scan_entail_wit_3_2.
Axiom proof_of_graham_scan_return_wit_1 : graham_scan_return_wit_1.
Axiom proof_of_graham_scan_partial_solve_wit_1 : graham_scan_partial_solve_wit_1.
Axiom proof_of_graham_scan_partial_solve_wit_2 : graham_scan_partial_solve_wit_2.
Axiom proof_of_graham_scan_partial_solve_wit_3 : graham_scan_partial_solve_wit_3.
Axiom proof_of_graham_scan_partial_solve_wit_4 : graham_scan_partial_solve_wit_4.
Axiom proof_of_graham_scan_partial_solve_wit_5 : graham_scan_partial_solve_wit_5.
Axiom proof_of_graham_scan_partial_solve_wit_6_pure : graham_scan_partial_solve_wit_6_pure.
Axiom proof_of_graham_scan_partial_solve_wit_6 : graham_scan_partial_solve_wit_6.
Axiom proof_of_graham_scan_partial_solve_wit_7 : graham_scan_partial_solve_wit_7.
Axiom proof_of_graham_scan_partial_solve_wit_8 : graham_scan_partial_solve_wit_8.
Axiom proof_of_graham_scan_partial_solve_wit_9 : graham_scan_partial_solve_wit_9.
Axiom proof_of_graham_scan_partial_solve_wit_10 : graham_scan_partial_solve_wit_10.
Axiom proof_of_graham_scan_partial_solve_wit_11_pure : graham_scan_partial_solve_wit_11_pure.
Axiom proof_of_graham_scan_partial_solve_wit_11 : graham_scan_partial_solve_wit_11.
Axiom proof_of_graham_scan_partial_solve_wit_12_pure : graham_scan_partial_solve_wit_12_pure.
Axiom proof_of_graham_scan_partial_solve_wit_12 : graham_scan_partial_solve_wit_12.
Axiom proof_of_graham_scan_partial_solve_wit_13_pure : graham_scan_partial_solve_wit_13_pure.
Axiom proof_of_graham_scan_partial_solve_wit_13 : graham_scan_partial_solve_wit_13.
Axiom proof_of_build_hull_from_sorted_tail_derive_high_level_spec_by_low_level_spec : build_hull_from_sorted_tail_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
