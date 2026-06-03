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
Require Import SimpleC.EE.Applications_human.convex_hull.convex_hull_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.convex_hull Require Import point_array_strategy_goal.
From SimpleC.EE.Applications_human.convex_hull Require Import point_array_strategy_proof.

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
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) ,
  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (tail_rev))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre tail_rev )
  **  (PointArray.undef_full hull_pre (tail_n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_hull_from_sorted_tail_safety_wit_2 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) ,
  “ (tail_n_pre < 0) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (tail_rev))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre tail_rev )
  **  (PointArray.undef_full hull_pre (tail_n_pre + 1 ) )
|--
  “ False ”
.

Definition build_hull_from_sorted_tail_safety_wit_3 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) ,
  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (tail_rev))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((( &( "top" ) )) # Int  |->_)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre tail_rev )
  **  ((&((hull_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((hull_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.undef_seg hull_pre 1 (tail_n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_hull_from_sorted_tail_safety_wit_4 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (tail_n: Z) (top: Z) ,
  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ ((top + 1 ) = (Zlength ((scan_hull (pivot0) (tail_rev) ((tail_n - 1 )))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (scan_hull (pivot0) (tail_rev) ((tail_n - 1 ))) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  “ ((tail_n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (tail_n - 1 )) ”
.

Definition build_hull_from_sorted_tail_safety_wit_5 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (tail_n: Z) (top: Z) ,
  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ ((top + 1 ) = (Zlength ((scan_hull (pivot0) (tail_rev) ((tail_n - 1 )))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (scan_hull (pivot0) (tail_rev) ((tail_n - 1 ))) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_hull_from_sorted_tail_safety_wit_6 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (top: Z) (tail_n: Z) (i: Z) ,
  “ ((-1) <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ ((top + 1 ) = (Zlength ((scan_hull (pivot0) (tail_rev) (i))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (scan_hull (pivot0) (tail_rev) (i)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_hull_from_sorted_tail_safety_wit_7 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (top: Z) (stk: (@list Point)) (tail_n: Z) (i: Z)  __default_Point ,
  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ ((top + 1 ) = (Zlength ((stack_norm (stk))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (stack_norm (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_hull_from_sorted_tail_safety_wit_8 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (stk: (@list Point)) (prefix: (@list Point)) (prev_pt: Point) (cur_pt: Point) (top: Z) (i: Z) (tail_n: Z)  __default_Point ,
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ ((top + 1 ) = (Zlength ((stack_norm (stk))))) ” 
  &&  “ ((stack_norm (stk)) = (app (prefix) ((cons (prev_pt) ((cons (cur_pt) (nil))))))) ” 
  &&  “ ((top - 1 ) = (Zlength (prefix))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top - 1 ) prefix )
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (prev_pt.(x) ))
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (prev_pt.(y) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (cur_pt.(x) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (cur_pt.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  “ ((top - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top - 1 )) ”
.

Definition build_hull_from_sorted_tail_safety_wit_9 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (stk: (@list Point)) (prefix: (@list Point)) (prev_pt: Point) (cur_pt: Point) (top: Z) (i: Z) (tail_n: Z)  __default_Point ,
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ ((top + 1 ) = (Zlength ((stack_norm (stk))))) ” 
  &&  “ ((stack_norm (stk)) = (app (prefix) ((cons (prev_pt) ((cons (cur_pt) (nil))))))) ” 
  &&  “ ((top - 1 ) = (Zlength (prefix))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top - 1 ) prefix )
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (prev_pt.(x) ))
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (prev_pt.(y) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (cur_pt.(x) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (cur_pt.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  “ ((top - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top - 1 )) ”
.

Definition build_hull_from_sorted_tail_safety_wit_10 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (stk: (@list Point)) (prefix: (@list Point)) (prev_pt: Point) (cur_pt: Point) (top: Z) (i: Z) (tail_n: Z)  __default_Point ,
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ ((top + 1 ) = (Zlength ((stack_norm (stk))))) ” 
  &&  “ ((stack_norm (stk)) = (app (prefix) ((cons (prev_pt) ((cons (cur_pt) (nil))))))) ” 
  &&  “ ((top - 1 ) = (Zlength (prefix))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top - 1 ) prefix )
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (prev_pt.(x) ))
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (prev_pt.(y) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (cur_pt.(x) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (cur_pt.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_hull_from_sorted_tail_safety_wit_11 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (stk: (@list Point)) (prefix: (@list Point)) (prev_pt: Point) (cur_pt: Point) (top: Z) (i: Z) (tail_n: Z)  __default_Point ,
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ ((top + 1 ) = (Zlength ((stack_norm (stk))))) ” 
  &&  “ ((stack_norm (stk)) = (app (prefix) ((cons (prev_pt) ((cons (cur_pt) (nil))))))) ” 
  &&  “ ((top - 1 ) = (Zlength (prefix))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top - 1 ) prefix )
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (prev_pt.(x) ))
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (prev_pt.(y) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (cur_pt.(x) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (cur_pt.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_hull_from_sorted_tail_safety_wit_12 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (stk: (@list Point)) (prefix: (@list Point)) (prev_pt: Point) (cur_pt: Point) (top: Z) (i: Z) (tail_n: Z) (retval: Z)  __default_Point ,
  “ (retval = (point_cross_by_value ((prev_pt.(x) )) ((prev_pt.(y) )) ((cur_pt.(x) )) ((cur_pt.(y) )) (((Znth i tail_rev __default_Point).(x) )) (((Znth i tail_rev __default_Point).(y) )))) ” 
  &&  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ ((top + 1 ) = (Zlength ((stack_norm (stk))))) ” 
  &&  “ ((stack_norm (stk)) = (app (prefix) ((cons (prev_pt) ((cons (cur_pt) (nil))))))) ” 
  &&  “ ((top - 1 ) = (Zlength (prefix))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top - 1 ) prefix )
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (prev_pt.(x) ))
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (prev_pt.(y) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (cur_pt.(x) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (cur_pt.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_hull_from_sorted_tail_safety_wit_13 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (stk: (@list Point)) (prefix: (@list Point)) (prev_pt: Point) (cur_pt: Point) (top: Z) (i: Z) (tail_n: Z) (retval: Z)  __default_Point ,
  “ (retval <= 0) ” 
  &&  “ (retval = (point_cross_by_value ((prev_pt.(x) )) ((prev_pt.(y) )) ((cur_pt.(x) )) ((cur_pt.(y) )) (((Znth i tail_rev __default_Point).(x) )) (((Znth i tail_rev __default_Point).(y) )))) ” 
  &&  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ ((top + 1 ) = (Zlength ((stack_norm (stk))))) ” 
  &&  “ ((stack_norm (stk)) = (app (prefix) ((cons (prev_pt) ((cons (cur_pt) (nil))))))) ” 
  &&  “ ((top - 1 ) = (Zlength (prefix))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top - 1 ) prefix )
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (prev_pt.(x) ))
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (prev_pt.(y) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (cur_pt.(x) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (cur_pt.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  “ ((top - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top - 1 )) ”
.

Definition build_hull_from_sorted_tail_safety_wit_14 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (stk: (@list Point)) (prefix: (@list Point)) (prev_pt: Point) (cur_pt: Point) (top: Z) (i: Z) (tail_n: Z) (retval: Z)  __default_Point ,
  “ (retval > 0) ” 
  &&  “ (retval = (point_cross_by_value ((prev_pt.(x) )) ((prev_pt.(y) )) ((cur_pt.(x) )) ((cur_pt.(y) )) (((Znth i tail_rev __default_Point).(x) )) (((Znth i tail_rev __default_Point).(y) )))) ” 
  &&  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ ((top + 1 ) = (Zlength ((stack_norm (stk))))) ” 
  &&  “ ((stack_norm (stk)) = (app (prefix) ((cons (prev_pt) ((cons (cur_pt) (nil))))))) ” 
  &&  “ ((top - 1 ) = (Zlength (prefix))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top - 1 ) prefix )
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (prev_pt.(x) ))
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (prev_pt.(y) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (cur_pt.(x) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (cur_pt.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  “ ((top + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top + 1 )) ”
.

Definition build_hull_from_sorted_tail_safety_wit_15 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (top: Z) (stk: (@list Point)) (tail_n: Z) (i: Z)  __default_Point ,
  “ (top < 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ ((top + 1 ) = (Zlength ((stack_norm (stk))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (stack_norm (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  “ ((top + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top + 1 )) ”
.

Definition build_hull_from_sorted_tail_safety_wit_16 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (i: Z) (tail_n: Z) (top: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ ((top + 1 ) = (Zlength ((scan_hull (pivot0) (tail_rev) ((i - 1 )))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (scan_hull (pivot0) (tail_rev) ((i - 1 ))) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition build_hull_from_sorted_tail_safety_wit_17 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (tail_n: Z) (top: Z) ,
  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ ((top + 1 ) = (Zlength ((final_hull (pivot0) ((rev (tail_rev))))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ” 
  &&  “ (is_convex_hull (rev (tail_rev)) (final_hull (pivot0) ((rev (tail_rev)))) ) ”
  &&  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (final_hull (pivot0) ((rev (tail_rev)))) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  “ ((top + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top + 1 )) ”
.

Definition build_hull_from_sorted_tail_safety_wit_18 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (tail_n: Z) (top: Z) ,
  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ ((top + 1 ) = (Zlength ((final_hull (pivot0) ((rev (tail_rev))))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ” 
  &&  “ (is_convex_hull (rev (tail_rev)) (final_hull (pivot0) ((rev (tail_rev)))) ) ”
  &&  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (final_hull (pivot0) ((rev (tail_rev)))) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_hull_from_sorted_tail_entail_wit_1 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) ,
  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (tail_rev))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre tail_rev )
  **  (PointArray.undef_full hull_pre (tail_n_pre + 1 ) )
|--
  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (tail_rev))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre tail_rev )
  **  (PointArray.undef_full hull_pre (tail_n_pre + 1 ) )
.

Definition build_hull_from_sorted_tail_entail_wit_2 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) ,
  “ (tail_n_pre >= 0) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (tail_rev))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre tail_rev )
  **  (PointArray.undef_full hull_pre (tail_n_pre + 1 ) )
|--
  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (tail_rev))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre tail_rev )
  **  ((&((hull_pre)  # "Point" ->ₛ "x")) # Int  |->_)
  **  ((&((hull_pre)  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.undef_seg hull_pre 1 (tail_n_pre + 1 ) )
.

Definition build_hull_from_sorted_tail_entail_wit_3 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) ,
  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (tail_rev))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre tail_rev )
  **  ((&((hull_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((hull_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.undef_seg hull_pre 1 (tail_n_pre + 1 ) )
|--
  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (tail_rev))) ” 
  &&  “ ((0 + 1 ) = (Zlength ((scan_hull (pivot0) (tail_rev) ((tail_n_pre - 1 )))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre tail_rev )
  **  (PointArray.seg hull_pre 0 (0 + 1 ) (scan_hull (pivot0) (tail_rev) ((tail_n_pre - 1 ))) )
  **  (PointArray.undef_seg hull_pre (0 + 1 ) (tail_n_pre + 1 ) )
.

Definition build_hull_from_sorted_tail_entail_wit_4 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (tail_n: Z) (top: Z) ,
  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ ((top + 1 ) = (Zlength ((scan_hull (pivot0) (tail_rev) ((tail_n - 1 )))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (scan_hull (pivot0) (tail_rev) ((tail_n - 1 ))) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  “ ((-1) <= (tail_n - 1 )) ” 
  &&  “ ((tail_n - 1 ) < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ ((top + 1 ) = (Zlength ((scan_hull (pivot0) (tail_rev) ((tail_n - 1 )))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (scan_hull (pivot0) (tail_rev) ((tail_n - 1 ))) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
.

Definition build_hull_from_sorted_tail_entail_wit_5 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (top: Z) (tail_n: Z) (i: Z)  __default_Point ,
  “ (i >= 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ ((top + 1 ) = (Zlength ((scan_hull (pivot0) (tail_rev) (i))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (scan_hull (pivot0) (tail_rev) (i)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  EX (stk: (@list Point)) ,
  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ ((top + 1 ) = (Zlength ((stack_norm (stk))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (stack_norm (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
.

Definition build_hull_from_sorted_tail_entail_wit_6 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (top: Z) (stk_2: (@list Point)) (tail_n: Z) (i: Z)  __default_Point ,
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk_2 ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk_2 ) ” 
  &&  “ ((top + 1 ) = (Zlength ((stack_norm (stk_2))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (stack_norm (stk_2)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  EX (prefix: (@list Point))  (prev_pt: Point)  (cur_pt: Point)  (stk: (@list Point)) ,
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ ((top + 1 ) = (Zlength ((stack_norm (stk))))) ” 
  &&  “ ((stack_norm (stk)) = (app (prefix) ((cons (prev_pt) ((cons (cur_pt) (nil))))))) ” 
  &&  “ ((top - 1 ) = (Zlength (prefix))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top - 1 ) prefix )
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (prev_pt.(x) ))
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (prev_pt.(y) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (cur_pt.(x) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (cur_pt.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
.

Definition build_hull_from_sorted_tail_entail_wit_7 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (stk_2: (@list Point)) (prefix_2: (@list Point)) (prev_pt_2: Point) (cur_pt_2: Point) (top: Z) (i: Z) (tail_n: Z)  __default_Point ,
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk_2 ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk_2 ) ” 
  &&  “ ((top + 1 ) = (Zlength ((stack_norm (stk_2))))) ” 
  &&  “ ((stack_norm (stk_2)) = (app (prefix_2) ((cons (prev_pt_2) ((cons (cur_pt_2) (nil))))))) ” 
  &&  “ ((top - 1 ) = (Zlength (prefix_2))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top - 1 ) prefix_2 )
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (prev_pt_2.(x) ))
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (prev_pt_2.(y) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (cur_pt_2.(x) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (cur_pt_2.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  EX (prefix: (@list Point))  (prev_pt: Point)  (cur_pt: Point)  (stk: (@list Point)) ,
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ ((top + 1 ) = (Zlength ((stack_norm (stk))))) ” 
  &&  “ ((stack_norm (stk)) = (app (prefix) ((cons (prev_pt) ((cons (cur_pt) (nil))))))) ” 
  &&  “ ((top - 1 ) = (Zlength (prefix))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top - 1 ) prefix )
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (prev_pt.(x) ))
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (prev_pt.(y) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (cur_pt.(x) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (cur_pt.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
.

Definition build_hull_from_sorted_tail_entail_wit_8 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (stk_2: (@list Point)) (prefix: (@list Point)) (prev_pt: Point) (cur_pt: Point) (top: Z) (i: Z) (tail_n: Z) (retval: Z)  __default_Point ,
  “ (retval <= 0) ” 
  &&  “ (retval = (point_cross_by_value ((prev_pt.(x) )) ((prev_pt.(y) )) ((cur_pt.(x) )) ((cur_pt.(y) )) (((Znth i tail_rev __default_Point).(x) )) (((Znth i tail_rev __default_Point).(y) )))) ” 
  &&  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk_2 ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk_2 ) ” 
  &&  “ ((top + 1 ) = (Zlength ((stack_norm (stk_2))))) ” 
  &&  “ ((stack_norm (stk_2)) = (app (prefix) ((cons (prev_pt) ((cons (cur_pt) (nil))))))) ” 
  &&  “ ((top - 1 ) = (Zlength (prefix))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top - 1 ) prefix )
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (prev_pt.(x) ))
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (prev_pt.(y) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (cur_pt.(x) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (cur_pt.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  EX (stk: (@list Point)) ,
  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (((top - 1 ) + 1 ) = (Zlength ((stack_norm (stk))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 ((top - 1 ) + 1 ) (stack_norm (stk)) )
  **  (PointArray.undef_seg hull_pre ((top - 1 ) + 1 ) (tail_n + 1 ) )
.

Definition build_hull_from_sorted_tail_entail_wit_9_1 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (stk_2: (@list Point)) (prefix: (@list Point)) (prev_pt: Point) (cur_pt: Point) (top: Z) (i: Z) (tail_n: Z) (retval: Z)  __default_Point ,
  “ (retval > 0) ” 
  &&  “ (retval = (point_cross_by_value ((prev_pt.(x) )) ((prev_pt.(y) )) ((cur_pt.(x) )) ((cur_pt.(y) )) (((Znth i tail_rev __default_Point).(x) )) (((Znth i tail_rev __default_Point).(y) )))) ” 
  &&  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk_2 ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk_2 ) ” 
  &&  “ ((top + 1 ) = (Zlength ((stack_norm (stk_2))))) ” 
  &&  “ ((stack_norm (stk_2)) = (app (prefix) ((cons (prev_pt) ((cons (cur_pt) (nil))))))) ” 
  &&  “ ((top - 1 ) = (Zlength (prefix))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top - 1 ) prefix )
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (prev_pt.(x) ))
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (prev_pt.(y) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (cur_pt.(x) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (cur_pt.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  EX (stk: (@list Point)) ,
  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_ready (Znth i tail_rev __default_Point) stk ) ” 
  &&  “ ((top + 1 ) = (Zlength ((stack_norm (stk))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (stack_norm (stk)) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |->_)
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n + 1 ) )
.

Definition build_hull_from_sorted_tail_entail_wit_9_2 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (top: Z) (stk_2: (@list Point)) (tail_n: Z) (i: Z)  __default_Point ,
  “ (top < 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk_2 ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk_2 ) ” 
  &&  “ ((top + 1 ) = (Zlength ((stack_norm (stk_2))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (stack_norm (stk_2)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  EX (stk: (@list Point)) ,
  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_ready (Znth i tail_rev __default_Point) stk ) ” 
  &&  “ ((top + 1 ) = (Zlength ((stack_norm (stk))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (stack_norm (stk)) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |->_)
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n + 1 ) )
.

Definition build_hull_from_sorted_tail_entail_wit_10 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (stk_2: (@list Point)) (i: Z) (tail_n: Z) (top: Z)  __default_Point ,
  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk_2 ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk_2 ) ” 
  &&  “ (stack_pop_ready (Znth i tail_rev __default_Point) stk_2 ) ” 
  &&  “ (top = (Zlength ((stack_norm (stk_2))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 top (stack_norm (stk_2)) )
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  EX (stk: (@list Point)) ,
  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_ready (Znth i tail_rev __default_Point) stk ) ” 
  &&  “ (top = (Zlength ((stack_norm (stk))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |->_)
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 top (stack_norm (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
.

Definition build_hull_from_sorted_tail_entail_wit_11 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (stk_2: (@list Point)) (i: Z) (tail_n: Z) (top: Z)  __default_Point ,
  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk_2 ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk_2 ) ” 
  &&  “ (stack_pop_ready (Znth i tail_rev __default_Point) stk_2 ) ” 
  &&  “ (top = (Zlength ((stack_norm (stk_2))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 top (stack_norm (stk_2)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  EX (stk: (@list Point)) ,
  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_ready (Znth i tail_rev __default_Point) stk ) ” 
  &&  “ (top = (Zlength ((stack_norm (stk))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 top (stack_norm (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
.

Definition build_hull_from_sorted_tail_entail_wit_12 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (stk: (@list Point)) (i: Z) (tail_n: Z) (top: Z)  __default_Point ,
  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_ready (Znth i tail_rev __default_Point) stk ) ” 
  &&  “ (top = (Zlength ((stack_norm (stk))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 top (stack_norm (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ ((top + 1 ) = (Zlength ((scan_hull (pivot0) (tail_rev) ((i - 1 )))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (scan_hull (pivot0) (tail_rev) ((i - 1 ))) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
.

Definition build_hull_from_sorted_tail_entail_wit_13 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (i: Z) (tail_n: Z) (top: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ ((top + 1 ) = (Zlength ((scan_hull (pivot0) (tail_rev) ((i - 1 )))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (scan_hull (pivot0) (tail_rev) ((i - 1 ))) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ ((top + 1 ) = (Zlength ((scan_hull (pivot0) (tail_rev) ((i - 1 )))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (scan_hull (pivot0) (tail_rev) ((i - 1 ))) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
.

Definition build_hull_from_sorted_tail_entail_wit_14 := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (top: Z) (tail_n: Z) (i: Z) ,
  “ (i < 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ ((top + 1 ) = (Zlength ((scan_hull (pivot0) (tail_rev) (i))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (scan_hull (pivot0) (tail_rev) (i)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ ((top + 1 ) = (Zlength ((final_hull (pivot0) ((rev (tail_rev))))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ” 
  &&  “ (is_convex_hull (rev (tail_rev)) (final_hull (pivot0) ((rev (tail_rev)))) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (final_hull (pivot0) ((rev (tail_rev)))) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
.

Definition build_hull_from_sorted_tail_return_wit_1 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (tail_n: Z) (top: Z) ,
  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ ((top + 1 ) = (Zlength ((final_hull (pivot0) ((rev (tail_rev))))))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ” 
  &&  “ (is_convex_hull (rev (tail_rev)) (final_hull (pivot0) ((rev (tail_rev)))) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (final_hull (pivot0) ((rev (tail_rev)))) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  “ ((top + 1 ) = (Zlength ((final_hull (pivot0) ((rev (tail_rev))))))) ” 
  &&  “ (is_convex_hull (rev (tail_rev)) (final_hull (pivot0) ((rev (tail_rev)))) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full sorted_tail_pre tail_n_pre tail_rev )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (final_hull (pivot0) ((rev (tail_rev)))) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
.

Definition build_hull_from_sorted_tail_partial_solve_wit_1_pure := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (stk: (@list Point)) (prefix: (@list Point)) (prev_pt: Point) (cur_pt: Point) (top: Z) (i: Z) (tail_n: Z)  __default_Point ,
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ ((top + 1 ) = (Zlength ((stack_norm (stk))))) ” 
  &&  “ ((stack_norm (stk)) = (app (prefix) ((cons (prev_pt) ((cons (cur_pt) (nil))))))) ” 
  &&  “ ((top - 1 ) = (Zlength (prefix))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top - 1 ) prefix )
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (prev_pt.(x) ))
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (prev_pt.(y) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (cur_pt.(x) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (cur_pt.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  “ (((Znth i tail_rev __default_Point).(y) ) <= point_bound) ” 
  &&  “ ((-point_bound) <= ((Znth i tail_rev __default_Point).(y) )) ” 
  &&  “ (((Znth i tail_rev __default_Point).(x) ) <= point_bound) ” 
  &&  “ ((-point_bound) <= ((Znth i tail_rev __default_Point).(x) )) ” 
  &&  “ ((cur_pt.(y) ) <= point_bound) ” 
  &&  “ ((-point_bound) <= (cur_pt.(y) )) ” 
  &&  “ ((cur_pt.(x) ) <= point_bound) ” 
  &&  “ ((-point_bound) <= (cur_pt.(x) )) ” 
  &&  “ ((prev_pt.(y) ) <= point_bound) ” 
  &&  “ ((-point_bound) <= (prev_pt.(y) )) ” 
  &&  “ ((prev_pt.(x) ) <= point_bound) ” 
  &&  “ ((-point_bound) <= (prev_pt.(x) )) ”
.

Definition build_hull_from_sorted_tail_partial_solve_wit_1_aux := 
forall (hull_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (tail_rev: (@list Point)) (pivot0: Point) (stk: (@list Point)) (prefix: (@list Point)) (prev_pt: Point) (cur_pt: Point) (top: Z) (i: Z) (tail_n: Z)  __default_Point ,
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ ((top + 1 ) = (Zlength ((stack_norm (stk))))) ” 
  &&  “ ((stack_norm (stk)) = (app (prefix) ((cons (prev_pt) ((cons (cur_pt) (nil))))))) ” 
  &&  “ ((top - 1 ) = (Zlength (prefix))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top - 1 ) prefix )
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (prev_pt.(x) ))
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (prev_pt.(y) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (cur_pt.(x) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (cur_pt.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
|--
  “ (((Znth i tail_rev __default_Point).(y) ) <= point_bound) ” 
  &&  “ ((-point_bound) <= ((Znth i tail_rev __default_Point).(y) )) ” 
  &&  “ (((Znth i tail_rev __default_Point).(x) ) <= point_bound) ” 
  &&  “ ((-point_bound) <= ((Znth i tail_rev __default_Point).(x) )) ” 
  &&  “ ((cur_pt.(y) ) <= point_bound) ” 
  &&  “ ((-point_bound) <= (cur_pt.(y) )) ” 
  &&  “ ((cur_pt.(x) ) <= point_bound) ” 
  &&  “ ((-point_bound) <= (cur_pt.(x) )) ” 
  &&  “ ((prev_pt.(y) ) <= point_bound) ” 
  &&  “ ((-point_bound) <= (prev_pt.(y) )) ” 
  &&  “ ((prev_pt.(x) ) <= point_bound) ” 
  &&  “ ((-point_bound) <= (prev_pt.(x) )) ” 
  &&  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n) ” 
  &&  “ (0 <= tail_n) ” 
  &&  “ (tail_n < INT_MAX) ” 
  &&  “ (tail_n = (Zlength (tail_rev))) ” 
  &&  “ (stack_suffix (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ (stack_pop_cursor (Znth i tail_rev __default_Point) (scan_stack (pivot0) (tail_rev) (i)) stk ) ” 
  &&  “ ((top + 1 ) = (Zlength ((stack_norm (stk))))) ” 
  &&  “ ((stack_norm (stk)) = (app (prefix) ((cons (prev_pt) ((cons (cur_pt) (nil))))))) ” 
  &&  “ ((top - 1 ) = (Zlength (prefix))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i tail_rev __default_Point).(x) ))
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i tail_rev __default_Point).(y) ))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n tail_rev )
  **  (PointArray.seg hull_pre 0 (top - 1 ) prefix )
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (prev_pt.(x) ))
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (prev_pt.(y) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> (cur_pt.(x) ))
  **  ((&(((hull_pre + (top * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> (cur_pt.(y) ))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n + 1 ) )
.

Definition build_hull_from_sorted_tail_partial_solve_wit_1 := build_hull_from_sorted_tail_partial_solve_wit_1_pure -> build_hull_from_sorted_tail_partial_solve_wit_1_aux.

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
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (i: Z) (j: Z) (n: Z) (pts: Z)  __default_Point ,
  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n) ” 
  &&  “ ((Zlength (pts_l)) = n) ”
  &&  ((&(((pts + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth j pts_l __default_Point).(x) ))
  **  ((&(((pts + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth j pts_l __default_Point).(y) ))
  **  ((&(((pts + (j * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i pts_l __default_Point).(x) ))
  **  ((&(((pts + (j * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i pts_l __default_Point).(y) ))
  **  (PointArray.seg pts 0 i (sublist (0) (i) (pts_l)) )
  **  (PointArray.seg pts (i + 1 ) j (sublist ((i + 1 )) (j) (pts_l)) )
  **  (PointArray.seg pts (j + 1 ) n (sublist ((j + 1 )) (n) (pts_l)) )
|--
  “ ((Zlength (pts_l)) = n_pre) ”
  &&  (PointArray.full pts_pre n_pre (point_swap (pts_l) (i_pre) (j_pre)) )
.

Definition swap_points_return_wit_2 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (j: Z) (i: Z) (n: Z) (pts: Z)  __default_Point ,
  “ (0 <= j) ” 
  &&  “ (j < i) ” 
  &&  “ (i < n) ” 
  &&  “ ((Zlength (pts_l)) = n) ”
  &&  ((&(((pts + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth j pts_l __default_Point).(x) ))
  **  ((&(((pts + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth j pts_l __default_Point).(y) ))
  **  ((&(((pts + (j * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i pts_l __default_Point).(x) ))
  **  ((&(((pts + (j * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i pts_l __default_Point).(y) ))
  **  (PointArray.seg pts 0 j (sublist (0) (j) (pts_l)) )
  **  (PointArray.seg pts (j + 1 ) i (sublist ((j + 1 )) (i) (pts_l)) )
  **  (PointArray.seg pts (i + 1 ) n (sublist ((i + 1 )) (n) (pts_l)) )
|--
  “ ((Zlength (pts_l)) = n_pre) ”
  &&  (PointArray.full pts_pre n_pre (point_swap (pts_l) (i_pre) (j_pre)) )
.

(*----- Function partition_polar_points -----*)

Definition partition_polar_points_safety_wit_1 := 
forall (pts_l: (@list Point)) (low: Z) (high: Z) (n: Z) (gy: Z) (gx: Z) (pts: Z)  __default_Point ,
  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "pivot_y" ) )) # Int  |-> ((Znth high pts_l __default_Point).(y) ))
  **  ((( &( "pivot_x" ) )) # Int  |-> ((Znth high pts_l __default_Point).(x) ))
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pts" ) )) # Ptr  |-> pts)
  **  ((&(((pts + (high * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth high pts_l __default_Point).(x) ))
  **  ((&(((pts + (high * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth high pts_l __default_Point).(y) ))
  **  (PointArray.missing_i pts high 0 n pts_l )
|--
  “ ((low - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (low - 1 )) ”
.

Definition partition_polar_points_safety_wit_2 := 
forall (pts_l: (@list Point)) (low: Z) (high: Z) (n: Z) (gy: Z) (gx: Z) (pts: Z)  __default_Point ,
  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "pivot_y" ) )) # Int  |-> ((Znth high pts_l __default_Point).(y) ))
  **  ((( &( "pivot_x" ) )) # Int  |-> ((Znth high pts_l __default_Point).(x) ))
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pts" ) )) # Ptr  |-> pts)
  **  ((&(((pts + (high * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth high pts_l __default_Point).(x) ))
  **  ((&(((pts + (high * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth high pts_l __default_Point).(y) ))
  **  (PointArray.missing_i pts high 0 n pts_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_polar_points_safety_wit_3 := 
forall (pts_l: (@list Point)) (pts_cur: (@list Point)) (n: Z) (low: Z) (high: Z) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z) (gy: Z) (gx: Z) (pts: Z) (retval: Z)  __default_Point ,
  “ (retval = (point_cmp_polar ((point_mk (gx) (gy))) ((point_mk (ax) (ay))) ((point_mk (pivot_x) (pivot_y))))) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ (low <= j) ” 
  &&  “ (j < high) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "c" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "ax" ) )) # Int  |-> ax)
  **  ((( &( "ay" ) )) # Int  |-> ay)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pts" ) )) # Ptr  |-> pts)
  **  (PointArray.full pts n pts_cur )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition partition_polar_points_safety_wit_4 := 
forall (pts_l: (@list Point)) (pts_cur: (@list Point)) (n: Z) (low: Z) (high: Z) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z) (gy: Z) (gx: Z) (pts: Z) (retval: Z)  __default_Point ,
  “ (retval <= 0) ” 
  &&  “ (retval = (point_cmp_polar ((point_mk (gx) (gy))) ((point_mk (ax) (ay))) ((point_mk (pivot_x) (pivot_y))))) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ (low <= j) ” 
  &&  “ (j < high) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "c" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "ax" ) )) # Int  |-> ax)
  **  ((( &( "ay" ) )) # Int  |-> ay)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pts" ) )) # Ptr  |-> pts)
  **  (PointArray.full pts n pts_cur )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_polar_points_safety_wit_5 := 
forall (pts_l: (@list Point)) (pts_cur: (@list Point)) (n: Z) (low: Z) (high: Z) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z) (gy: Z) (gx: Z) (pts: Z) (retval: Z)  __default_Point ,
  “ (retval > 0) ” 
  &&  “ (retval = (point_cmp_polar ((point_mk (gx) (gy))) ((point_mk (ax) (ay))) ((point_mk (pivot_x) (pivot_y))))) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ (low <= j) ” 
  &&  “ (j < high) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pts" ) )) # Ptr  |-> pts)
  **  (PointArray.full pts n pts_cur )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition partition_polar_points_safety_wit_6 := 
forall (pts_l: (@list Point)) (pts_cur: (@list Point)) (n: Z) (low: Z) (high: Z) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z) (gy: Z) (gx: Z) (pts: Z) (retval: Z)  __default_Point ,
  “ ((i + 1 ) = j) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (retval = (point_cmp_polar ((point_mk (gx) (gy))) ((point_mk (ax) (ay))) ((point_mk (pivot_x) (pivot_y))))) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ (low <= j) ” 
  &&  “ (j < high) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pts" ) )) # Ptr  |-> pts)
  **  (PointArray.full pts n pts_cur )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition partition_polar_points_safety_wit_7 := 
forall (pts_l: (@list Point)) (pts_cur: (@list Point)) (n: Z) (low: Z) (high: Z) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z) (gy: Z) (gx: Z) (pts: Z) (retval: Z)  __default_Point ,
  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ ((i + 1 ) <> j) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (retval = (point_cmp_polar ((point_mk (gx) (gy))) ((point_mk (ax) (ay))) ((point_mk (pivot_x) (pivot_y))))) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ (low <= j) ” 
  &&  “ (j < high) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts n (point_swap (pts_cur) ((i + 1 )) (j)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pts" ) )) # Ptr  |-> pts)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition partition_polar_points_safety_wit_8 := 
forall (pts_l: (@list Point)) (pts: Z) (gx: Z) (gy: Z) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (high: Z) (low: Z) (n: Z) (pts_cur: (@list Point))  __default_Point ,
  “ (j >= high) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pts" ) )) # Ptr  |-> pts)
  **  (PointArray.full pts n pts_cur )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_polar_points_safety_wit_9 := 
forall (pts_l: (@list Point)) (pts: Z) (gx: Z) (gy: Z) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (high: Z) (low: Z) (n: Z) (pts_cur: (@list Point))  __default_Point ,
  “ (j >= high) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pts" ) )) # Ptr  |-> pts)
  **  (PointArray.full pts n pts_cur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_polar_points_safety_wit_10 := 
forall (pts_l: (@list Point)) (pts: Z) (gx: Z) (gy: Z) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (high: Z) (low: Z) (n: Z) (pts_cur: (@list Point))  __default_Point ,
  “ ((i + 1 ) <> high) ” 
  &&  “ (j >= high) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pts" ) )) # Ptr  |-> pts)
  **  (PointArray.full pts n pts_cur )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_polar_points_safety_wit_11 := 
forall (pts_l: (@list Point)) (pts: Z) (gx: Z) (gy: Z) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (high: Z) (low: Z) (n: Z) (pts_cur: (@list Point))  __default_Point ,
  “ ((i + 1 ) <> high) ” 
  &&  “ (j >= high) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pts" ) )) # Ptr  |-> pts)
  **  (PointArray.full pts n pts_cur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_polar_points_safety_wit_12 := 
forall (pts_l: (@list Point)) (pts: Z) (gx: Z) (gy: Z) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (high: Z) (low: Z) (n: Z) (pts_cur: (@list Point))  __default_Point ,
  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ ((i + 1 ) <> high) ” 
  &&  “ (j >= high) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts n (point_swap (pts_cur) ((i + 1 )) (high)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pts" ) )) # Ptr  |-> pts)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_polar_points_safety_wit_13 := 
forall (pts_l: (@list Point)) (pts: Z) (gx: Z) (gy: Z) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (high: Z) (low: Z) (n: Z) (pts_cur: (@list Point))  __default_Point ,
  “ ((i + 1 ) = high) ” 
  &&  “ (j >= high) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pts" ) )) # Ptr  |-> pts)
  **  (PointArray.full pts n pts_cur )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_polar_points_safety_wit_14 := 
forall (pts_l: (@list Point)) (pts: Z) (gx: Z) (gy: Z) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (high: Z) (low: Z) (n: Z) (pts_cur: (@list Point))  __default_Point ,
  “ ((i + 1 ) = high) ” 
  &&  “ (j >= high) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pts" ) )) # Ptr  |-> pts)
  **  (PointArray.full pts n pts_cur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_polar_points_safety_wit_15 := 
forall (pts_l: (@list Point)) (pts: Z) (gx: Z) (gy: Z) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (high: Z) (low: Z) (n: Z) (pts_cur: (@list Point))  __default_Point ,
  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ ((i + 1 ) <> high) ” 
  &&  “ (j >= high) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts n (point_swap (pts_cur) ((i + 1 )) (high)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pts" ) )) # Ptr  |-> pts)
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
forall (pts_l: (@list Point)) (low: Z) (high: Z) (n: Z) (gy: Z) (gx: Z) (pts: Z)  __default_Point ,
  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  ((&(((pts + (high * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth high pts_l __default_Point).(x) ))
  **  ((&(((pts + (high * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth high pts_l __default_Point).(y) ))
  **  (PointArray.missing_i pts high 0 n pts_l )
|--
  EX (pts_cur: (@list Point)) ,
  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ ((low - 1 ) <= (low - 1 )) ” 
  &&  “ ((low - 1 ) < low) ” 
  &&  “ (low <= high) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = ((Znth high pts_l __default_Point).(x) )) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = ((Znth high pts_l __default_Point).(y) )) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (((Znth high pts_l __default_Point).(x) )) (((Znth high pts_l __default_Point).(y) ))) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (((Znth high pts_l __default_Point).(x) )) (((Znth high pts_l __default_Point).(y) ))) (low - 1 ) low ) ”
  &&  (PointArray.full pts n pts_cur )
.

Definition partition_polar_points_entail_wit_3 := 
forall (pts_l: (@list Point)) (pts: Z) (gx: Z) (gy: Z) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (high: Z) (low: Z) (n: Z) (pts_cur_2: (@list Point))  __default_Point ,
  “ (j < high) ” 
  &&  “ ((Zlength (pts_cur_2)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high) ” 
  &&  “ (((Znth high pts_cur_2 __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur_2 __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur_2 ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur_2 low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts n pts_cur_2 )
|--
  EX (pts_cur: (@list Point)) ,
  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ (low <= j) ” 
  &&  “ (j < high) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((&(((pts + (j * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth j pts_cur __default_Point).(x) ))
  **  ((&(((pts + (j * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth j pts_cur __default_Point).(y) ))
  **  (PointArray.missing_i pts j 0 n pts_cur )
.

Definition partition_polar_points_entail_wit_4 := 
forall (pts_l: (@list Point)) (pts_cur: (@list Point)) (n: Z) (low: Z) (high: Z) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (gy: Z) (gx: Z) (pts: Z)  __default_Point ,
  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ (low <= j) ” 
  &&  “ (j < high) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((&(((pts + (j * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth j pts_cur __default_Point).(x) ))
  **  ((&(((pts + (j * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth j pts_cur __default_Point).(y) ))
  **  (PointArray.missing_i pts j 0 n pts_cur )
|--
  EX (pts_cur_2: (@list Point)) ,
  “ ((Zlength (pts_cur_2)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ (low <= j) ” 
  &&  “ (j < high) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high pts_cur_2 __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur_2 __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur_2 __default_Point).(x) ) = ((Znth j pts_cur __default_Point).(x) )) ” 
  &&  “ (((Znth j pts_cur_2 __default_Point).(y) ) = ((Znth j pts_cur __default_Point).(y) )) ” 
  &&  “ (PointCoordsBound pts_cur_2 ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (((Znth j pts_cur __default_Point).(x) )) (((Znth j pts_cur __default_Point).(y) ))) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur_2 low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts n pts_cur_2 )
.

Definition partition_polar_points_entail_wit_5_1 := 
forall (pts_l: (@list Point)) (pts_cur_2: (@list Point)) (n: Z) (low: Z) (high: Z) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z) (gy: Z) (gx: Z) (pts: Z) (retval: Z)  __default_Point ,
  “ ((Zlength (pts_cur_2)) = n) ” 
  &&  “ ((i + 1 ) <> j) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (retval = (point_cmp_polar ((point_mk (gx) (gy))) ((point_mk (ax) (ay))) ((point_mk (pivot_x) (pivot_y))))) ” 
  &&  “ ((Zlength (pts_cur_2)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ (low <= j) ” 
  &&  “ (j < high) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high pts_cur_2 __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur_2 __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur_2 __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur_2 __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur_2 ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur_2 low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts n (point_swap (pts_cur_2) ((i + 1 )) (j)) )
|--
  EX (pts_cur: (@list Point)) ,
  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ ((low - 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < (j + 1 )) ” 
  &&  “ ((j + 1 ) <= high) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) (i + 1 ) (j + 1 ) ) ”
  &&  (PointArray.full pts n pts_cur )
.

Definition partition_polar_points_entail_wit_5_2 := 
forall (pts_l: (@list Point)) (pts_cur_2: (@list Point)) (n: Z) (low: Z) (high: Z) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z) (gy: Z) (gx: Z) (pts: Z) (retval: Z)  __default_Point ,
  “ ((i + 1 ) = j) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (retval = (point_cmp_polar ((point_mk (gx) (gy))) ((point_mk (ax) (ay))) ((point_mk (pivot_x) (pivot_y))))) ” 
  &&  “ ((Zlength (pts_cur_2)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ (low <= j) ” 
  &&  “ (j < high) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high pts_cur_2 __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur_2 __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur_2 __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur_2 __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur_2 ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur_2 low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts n pts_cur_2 )
|--
  EX (pts_cur: (@list Point)) ,
  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ ((low - 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < (j + 1 )) ” 
  &&  “ ((j + 1 ) <= high) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) (i + 1 ) (j + 1 ) ) ”
  &&  (PointArray.full pts n pts_cur )
.

Definition partition_polar_points_entail_wit_5_3 := 
forall (pts_l: (@list Point)) (pts_cur_2: (@list Point)) (n: Z) (low: Z) (high: Z) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z) (gy: Z) (gx: Z) (pts: Z) (retval: Z)  __default_Point ,
  “ (retval > 0) ” 
  &&  “ (retval = (point_cmp_polar ((point_mk (gx) (gy))) ((point_mk (ax) (ay))) ((point_mk (pivot_x) (pivot_y))))) ” 
  &&  “ ((Zlength (pts_cur_2)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ (low <= j) ” 
  &&  “ (j < high) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high pts_cur_2 __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur_2 __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur_2 __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur_2 __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur_2 ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur_2 low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts n pts_cur_2 )
|--
  EX (pts_cur: (@list Point)) ,
  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < (j + 1 )) ” 
  &&  “ ((j + 1 ) <= high) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i (j + 1 ) ) ”
  &&  (PointArray.full pts n pts_cur )
.

Definition partition_polar_points_return_wit_1 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts: Z) (gx: Z) (gy: Z) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (high: Z) (low: Z) (n: Z) (pts_cur: (@list Point))  __default_Point ,
  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ ((i + 1 ) <> high) ” 
  &&  “ (j >= high) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts n (point_swap (pts_cur) ((i + 1 )) (high)) )
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
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts: Z) (gx: Z) (gy: Z) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (high: Z) (low: Z) (n: Z) (pts_cur: (@list Point))  __default_Point ,
  “ ((i + 1 ) = high) ” 
  &&  “ (j >= high) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts n pts_cur )
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
forall (pts_l: (@list Point)) (pts_cur: (@list Point)) (n: Z) (low: Z) (high: Z) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z) (gy: Z) (gx: Z) (pts: Z)  __default_Point ,
  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ (low <= j) ” 
  &&  “ (j < high) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "ax" ) )) # Int  |-> ax)
  **  ((( &( "ay" ) )) # Int  |-> ay)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pts" ) )) # Ptr  |-> pts)
  **  (PointArray.full pts n pts_cur )
|--
  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ”
.

Definition partition_polar_points_partial_solve_wit_1_aux := 
forall (pts_l: (@list Point)) (pts_cur: (@list Point)) (n: Z) (low: Z) (high: Z) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z) (gy: Z) (gx: Z) (pts: Z)  __default_Point ,
  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ (low <= j) ” 
  &&  “ (j < high) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts n pts_cur )
|--
  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ (low <= j) ” 
  &&  “ (j < high) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts n pts_cur )
.

Definition partition_polar_points_partial_solve_wit_1 := partition_polar_points_partial_solve_wit_1_pure -> partition_polar_points_partial_solve_wit_1_aux.

Definition partition_polar_points_partial_solve_wit_2_pure := 
forall (pts_l: (@list Point)) (pts_cur: (@list Point)) (n: Z) (low: Z) (high: Z) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z) (gy: Z) (gx: Z) (pts: Z) (retval: Z)  __default_Point ,
  “ ((i + 1 ) <> j) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (retval = (point_cmp_polar ((point_mk (gx) (gy))) ((point_mk (ax) (ay))) ((point_mk (pivot_x) (pivot_y))))) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ (low <= j) ” 
  &&  “ (j < high) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "c" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "ax" ) )) # Int  |-> ax)
  **  ((( &( "ay" ) )) # Int  |-> ay)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pts" ) )) # Ptr  |-> pts)
  **  (PointArray.full pts n pts_cur )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n) ” 
  &&  “ ((i + 1 ) <> j) ” 
  &&  “ ((Zlength (pts_cur)) = n) ”
.

Definition partition_polar_points_partial_solve_wit_2_aux := 
forall (pts_l: (@list Point)) (pts_cur: (@list Point)) (n: Z) (low: Z) (high: Z) (j: Z) (i: Z) (pivot_x: Z) (pivot_y: Z) (ax: Z) (ay: Z) (gy: Z) (gx: Z) (pts: Z) (retval: Z)  __default_Point ,
  “ ((i + 1 ) <> j) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (retval = (point_cmp_polar ((point_mk (gx) (gy))) ((point_mk (ax) (ay))) ((point_mk (pivot_x) (pivot_y))))) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ (low <= j) ” 
  &&  “ (j < high) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts n pts_cur )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n) ” 
  &&  “ ((i + 1 ) <> j) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ ((i + 1 ) <> j) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (retval = (point_cmp_polar ((point_mk (gx) (gy))) ((point_mk (ax) (ay))) ((point_mk (pivot_x) (pivot_y))))) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ (low <= j) ” 
  &&  “ (j < high) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth j pts_cur __default_Point).(x) ) = ax) ” 
  &&  “ (((Znth j pts_cur __default_Point).(y) ) = ay) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk (ax) (ay)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts n pts_cur )
.

Definition partition_polar_points_partial_solve_wit_2 := partition_polar_points_partial_solve_wit_2_pure -> partition_polar_points_partial_solve_wit_2_aux.

Definition partition_polar_points_partial_solve_wit_3_pure := 
forall (pts_l: (@list Point)) (pts: Z) (gx: Z) (gy: Z) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (high: Z) (low: Z) (n: Z) (pts_cur: (@list Point))  __default_Point ,
  “ ((i + 1 ) <> high) ” 
  &&  “ (j >= high) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pts" ) )) # Ptr  |-> pts)
  **  (PointArray.full pts n pts_cur )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n) ” 
  &&  “ (0 <= high) ” 
  &&  “ (high < n) ” 
  &&  “ ((i + 1 ) <> high) ” 
  &&  “ ((Zlength (pts_cur)) = n) ”
.

Definition partition_polar_points_partial_solve_wit_3_aux := 
forall (pts_l: (@list Point)) (pts: Z) (gx: Z) (gy: Z) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (high: Z) (low: Z) (n: Z) (pts_cur: (@list Point))  __default_Point ,
  “ ((i + 1 ) <> high) ” 
  &&  “ (j >= high) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts n pts_cur )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n) ” 
  &&  “ (0 <= high) ” 
  &&  “ (high < n) ” 
  &&  “ ((i + 1 ) <> high) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ ((i + 1 ) <> high) ” 
  &&  “ (j >= high) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= high) ” 
  &&  “ (high < n) ” 
  &&  “ ((low - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high) ” 
  &&  “ (((Znth high pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (PointPolarPartitionScanInv (point_mk (gx) (gy)) pts_l pts_cur low high (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts n pts_cur )
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

(*----- Function sort_and_build_hull -----*)

Definition sort_and_build_hull_safety_wit_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((( &( "pivot_idx" ) )) # Int  |->_)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n_pre pts_l )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_and_build_hull_safety_wit_2 := 
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
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n_pre pts_l )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_and_build_hull_safety_wit_3 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (n: Z) (i: Z) (pivot_idx: Z) (ax: Z) (ay: Z) (bx: Z) (b_y_val: Z) (retval: Z)  __default_Point ,
  “ (retval = (point_cmp_leftdown ((point_mk (ax) (ay))) ((point_mk (bx) (b_y_val))))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (ax = ((Znth i pts_l __default_Point).(x) )) ” 
  &&  “ (ay = ((Znth i pts_l __default_Point).(y) )) ” 
  &&  “ (bx = ((Znth pivot_idx pts_l __default_Point).(x) )) ” 
  &&  “ (b_y_val = ((Znth pivot_idx pts_l __default_Point).(y) )) ”
  &&  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((( &( "ax" ) )) # Int  |-> ax)
  **  ((( &( "ay" ) )) # Int  |-> ay)
  **  ((( &( "bx" ) )) # Int  |-> bx)
  **  ((( &( "b_y_val" ) )) # Int  |-> b_y_val)
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_and_build_hull_safety_wit_4 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (n: Z) (i: Z) (pivot_idx: Z) (ax: Z) (ay: Z) (bx: Z) (b_y_val: Z) (retval: Z)  __default_Point ,
  “ (retval >= 0) ” 
  &&  “ (retval = (point_cmp_leftdown ((point_mk (ax) (ay))) ((point_mk (bx) (b_y_val))))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (ax = ((Znth i pts_l __default_Point).(x) )) ” 
  &&  “ (ay = ((Znth i pts_l __default_Point).(y) )) ” 
  &&  “ (bx = ((Znth pivot_idx pts_l __default_Point).(x) )) ” 
  &&  “ (b_y_val = ((Znth pivot_idx pts_l __default_Point).(y) )) ”
  &&  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sort_and_build_hull_safety_wit_5 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (n: Z) (i: Z) (pivot_idx: Z) (ax: Z) (ay: Z) (bx: Z) (b_y_val: Z) (retval: Z)  __default_Point ,
  “ (retval < 0) ” 
  &&  “ (retval = (point_cmp_leftdown ((point_mk (ax) (ay))) ((point_mk (bx) (b_y_val))))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (ax = ((Znth i pts_l __default_Point).(x) )) ” 
  &&  “ (ay = ((Znth i pts_l __default_Point).(y) )) ” 
  &&  “ (bx = ((Znth pivot_idx pts_l __default_Point).(x) )) ” 
  &&  “ (b_y_val = ((Znth pivot_idx pts_l __default_Point).(y) )) ”
  &&  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_idx" ) )) # Int  |-> i)
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sort_and_build_hull_safety_wit_6 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (n: Z) (pivot_idx: Z) ,
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ”
  &&  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_and_build_hull_safety_wit_7 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (n: Z) (pivot_idx: Z) ,
  “ (pivot_idx <> 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ”
  &&  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_and_build_hull_safety_wit_8 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot: (@list Point)) (n: Z) (pivot_idx: Z)  __default_Point ,
  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_pivot)) = n) ” 
  &&  “ (PointCoordsBound pts_pivot ) ”
  &&  ((( &( "gx" ) )) # Int  |->_)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  ((&(((pts_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth 0 pts_pivot __default_Point).(x) ))
  **  ((&(((pts_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth 0 pts_pivot __default_Point).(y) ))
  **  (PointArray.missing_i pts_pre 0 0 n pts_pivot )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_and_build_hull_safety_wit_9 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot: (@list Point)) (n: Z) (pivot_idx: Z)  __default_Point ,
  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_pivot)) = n) ” 
  &&  “ (PointCoordsBound pts_pivot ) ”
  &&  ((( &( "gy" ) )) # Int  |->_)
  **  ((( &( "gx" ) )) # Int  |-> ((Znth 0 pts_pivot __default_Point).(x) ))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  ((&(((pts_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth 0 pts_pivot __default_Point).(x) ))
  **  ((&(((pts_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth 0 pts_pivot __default_Point).(y) ))
  **  (PointArray.missing_i pts_pre 0 0 n pts_pivot )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_and_build_hull_safety_wit_10 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot: (@list Point)) (n: Z) (pivot_idx: Z) (gx: Z) (gy: Z)  __default_Point ,
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_pivot)) = n) ” 
  &&  “ (PointCoordsBound pts_pivot ) ” 
  &&  “ (((Znth 0 pts_pivot __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_pivot __default_Point).(y) ) = gy) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.full pts_pre n pts_pivot )
  **  (PointArray.undef_full hull_pre n )
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition sort_and_build_hull_safety_wit_11 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot: (@list Point)) (n: Z) (pivot_idx: Z) (gx: Z) (gy: Z)  __default_Point ,
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_pivot)) = n) ” 
  &&  “ (PointCoordsBound pts_pivot ) ” 
  &&  “ (((Znth 0 pts_pivot __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_pivot __default_Point).(y) ) = gy) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.full pts_pre n pts_pivot )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_and_build_hull_safety_wit_12 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot: (@list Point)) (n: Z) (pivot_idx: Z) (gx: Z) (gy: Z)  __default_Point ,
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_pivot)) = n) ” 
  &&  “ (PointCoordsBound pts_pivot ) ” 
  &&  “ (((Znth 0 pts_pivot __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_pivot __default_Point).(y) ) = gy) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.full pts_pre n pts_pivot )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_and_build_hull_safety_wit_13 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot: (@list Point)) (pts_sorted: (@list Point)) (n: Z) (pivot_idx: Z) (gy: Z) (gx: Z)  __default_Point ,
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_sorted)) = n) ” 
  &&  “ (PointCoordsBound pts_sorted ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSameOutsideRange pts_pivot pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(y) ) = gy) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  ((( &( "rev_i" ) )) # Int  |->_)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.full pts_pre n pts_sorted )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_and_build_hull_safety_wit_14 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot: (@list Point)) (pts_sorted: (@list Point)) (n: Z) (pivot_idx: Z) (gy: Z) (gx: Z)  __default_Point ,
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_sorted)) = n) ” 
  &&  “ (PointCoordsBound pts_sorted ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSameOutsideRange pts_pivot pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(y) ) = gy) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  ((( &( "rev_j" ) )) # Int  |->_)
  **  ((( &( "rev_i" ) )) # Int  |-> 1)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.full pts_pre n pts_sorted )
  **  (PointArray.undef_full hull_pre n )
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition sort_and_build_hull_safety_wit_15 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot: (@list Point)) (pts_sorted: (@list Point)) (n: Z) (pivot_idx: Z) (gy: Z) (gx: Z)  __default_Point ,
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_sorted)) = n) ” 
  &&  “ (PointCoordsBound pts_sorted ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSameOutsideRange pts_pivot pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(y) ) = gy) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  ((( &( "rev_j" ) )) # Int  |->_)
  **  ((( &( "rev_i" ) )) # Int  |-> 1)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.full pts_pre n pts_sorted )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_and_build_hull_safety_wit_16 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (gx: Z) (gy: Z) (pts_cur: (@list Point)) (pts_sorted: (@list Point)) (pivot_idx: Z) (pts_pivot: (@list Point)) (rev_j: Z) (rev_i: Z) (n: Z)  __default_Point ,
  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (rev_i < rev_j) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= rev_i) ” 
  &&  “ (rev_i <= n) ” 
  &&  “ (0 <= rev_j) ” 
  &&  “ (rev_j < n) ” 
  &&  “ (rev_j = (n - rev_i )) ” 
  &&  “ (rev_i <= (rev_j + 1 )) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_sorted)) = n) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (PointCoordsBound pts_sorted ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (PointTailReverseState pts_sorted pts_cur n rev_i rev_j ) ” 
  &&  “ (((Znth 0 pts_cur __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_cur __default_Point).(y) ) = gy) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  (PointArray.full pts_pre n (point_swap (pts_cur) (rev_i) (rev_j)) )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "rev_i" ) )) # Int  |-> rev_i)
  **  ((( &( "rev_j" ) )) # Int  |-> rev_j)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.undef_full hull_pre n )
|--
  “ ((rev_i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (rev_i + 1 )) ”
.

Definition sort_and_build_hull_safety_wit_17 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (gx: Z) (gy: Z) (pts_cur: (@list Point)) (pts_sorted: (@list Point)) (pivot_idx: Z) (pts_pivot: (@list Point)) (rev_j: Z) (rev_i: Z) (n: Z)  __default_Point ,
  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (rev_i < rev_j) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= rev_i) ” 
  &&  “ (rev_i <= n) ” 
  &&  “ (0 <= rev_j) ” 
  &&  “ (rev_j < n) ” 
  &&  “ (rev_j = (n - rev_i )) ” 
  &&  “ (rev_i <= (rev_j + 1 )) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_sorted)) = n) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (PointCoordsBound pts_sorted ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (PointTailReverseState pts_sorted pts_cur n rev_i rev_j ) ” 
  &&  “ (((Znth 0 pts_cur __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_cur __default_Point).(y) ) = gy) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  (PointArray.full pts_pre n (point_swap (pts_cur) (rev_i) (rev_j)) )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "rev_i" ) )) # Int  |-> (rev_i + 1 ))
  **  ((( &( "rev_j" ) )) # Int  |-> rev_j)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.undef_full hull_pre n )
|--
  “ ((rev_j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (rev_j - 1 )) ”
.

Definition sort_and_build_hull_safety_wit_18 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (gx: Z) (gy: Z) (pts_cur: (@list Point)) (pts_sorted: (@list Point)) (pivot_idx: Z) (pts_pivot: (@list Point)) (rev_j: Z) (rev_i: Z) (n: Z)  __default_Point ,
  “ (rev_i >= rev_j) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= rev_i) ” 
  &&  “ (rev_i <= n) ” 
  &&  “ (0 <= rev_j) ” 
  &&  “ (rev_j < n) ” 
  &&  “ (rev_j = (n - rev_i )) ” 
  &&  “ (rev_i <= (rev_j + 1 )) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_sorted)) = n) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (PointCoordsBound pts_sorted ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (PointTailReverseState pts_sorted pts_cur n rev_i rev_j ) ” 
  &&  “ (((Znth 0 pts_cur __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_cur __default_Point).(y) ) = gy) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  ((( &( "tail" ) )) # Ptr  |->_)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "rev_i" ) )) # Int  |-> rev_i)
  **  ((( &( "rev_j" ) )) # Int  |-> rev_j)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.full pts_pre n pts_cur )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_and_build_hull_safety_wit_19 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot: (@list Point)) (pts_sorted: (@list Point)) (pts_rev: (@list Point)) (tail_rev: (@list Point)) (pivot0: Point) (tail: Z) (n: Z) (gy: Z) (gx: Z) (pivot_idx: Z) (rev_j: Z) (rev_i: Z)  __default_Point ,
  “ (tail = (pts_pre + sizeof( "Point" ) )) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < INT_MAX) ” 
  &&  “ (pivot0 = (point_mk (gx) (gy))) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_rev)) = n) ” 
  &&  “ ((Zlength (tail_rev)) = (n - 1 )) ” 
  &&  “ (tail_rev = (sublist (1) (n) (pts_rev))) ” 
  &&  “ (PointCoordsBound pts_rev ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (PointTailReverseState pts_sorted pts_rev n rev_i rev_j ) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ” 
  &&  “ (((Znth 0 pts_rev __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_rev __default_Point).(y) ) = gy) ”
  &&  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "tail" ) )) # Ptr  |-> tail)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((( &( "rev_j" ) )) # Int  |-> rev_j)
  **  ((( &( "rev_i" ) )) # Int  |-> rev_i)
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.seg pts_pre 0 1 (cons ((point_mk (gx) (gy))) (nil)) )
  **  (PointArray.full tail (n - 1 ) tail_rev )
  **  (PointArray.undef_full hull_pre ((n - 1 ) + 1 ) )
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition sort_and_build_hull_safety_wit_20 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot: (@list Point)) (pts_sorted: (@list Point)) (pts_rev: (@list Point)) (tail_rev: (@list Point)) (pivot0: Point) (tail: Z) (n: Z) (gy: Z) (gx: Z) (pivot_idx: Z) (rev_j: Z) (rev_i: Z)  __default_Point ,
  “ (tail = (pts_pre + sizeof( "Point" ) )) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < INT_MAX) ” 
  &&  “ (pivot0 = (point_mk (gx) (gy))) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_rev)) = n) ” 
  &&  “ ((Zlength (tail_rev)) = (n - 1 )) ” 
  &&  “ (tail_rev = (sublist (1) (n) (pts_rev))) ” 
  &&  “ (PointCoordsBound pts_rev ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (PointTailReverseState pts_sorted pts_rev n rev_i rev_j ) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ” 
  &&  “ (((Znth 0 pts_rev __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_rev __default_Point).(y) ) = gy) ”
  &&  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "tail" ) )) # Ptr  |-> tail)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((( &( "rev_j" ) )) # Int  |-> rev_j)
  **  ((( &( "rev_i" ) )) # Int  |-> rev_i)
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.seg pts_pre 0 1 (cons ((point_mk (gx) (gy))) (nil)) )
  **  (PointArray.full tail (n - 1 ) tail_rev )
  **  (PointArray.undef_full hull_pre ((n - 1 ) + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_and_build_hull_entail_wit_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n_pre pts_l )
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
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n_pre pts_l )
  **  (PointArray.undef_full hull_pre n_pre )
.

Definition sort_and_build_hull_entail_wit_2 := 
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
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  ((&(((pts_pre + (pivot_idx * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth pivot_idx pts_l __default_Point).(x) ))
  **  ((&(((pts_pre + (pivot_idx * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth pivot_idx pts_l __default_Point).(y) ))
  **  ((&(((pts_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i pts_l __default_Point).(x) ))
  **  ((&(((pts_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i pts_l __default_Point).(y) ))
  **  (PointArray.seg pts_pre 0 pivot_idx (sublist (0) (pivot_idx) (pts_l)) )
  **  (PointArray.seg pts_pre (pivot_idx + 1 ) i (sublist ((pivot_idx + 1 )) (i) (pts_l)) )
  **  (PointArray.seg pts_pre (i + 1 ) n (sublist ((i + 1 )) (n) (pts_l)) )
  **  (PointArray.undef_full hull_pre n )
.

Definition sort_and_build_hull_entail_wit_3 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (n: Z) (i: Z) (pivot_idx: Z)  __default_Point ,
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  ((&(((pts_pre + (pivot_idx * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth pivot_idx pts_l __default_Point).(x) ))
  **  ((&(((pts_pre + (pivot_idx * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth pivot_idx pts_l __default_Point).(y) ))
  **  ((&(((pts_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth i pts_l __default_Point).(x) ))
  **  ((&(((pts_pre + (i * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth i pts_l __default_Point).(y) ))
  **  (PointArray.seg pts_pre 0 pivot_idx (sublist (0) (pivot_idx) (pts_l)) )
  **  (PointArray.seg pts_pre (pivot_idx + 1 ) i (sublist ((pivot_idx + 1 )) (i) (pts_l)) )
  **  (PointArray.seg pts_pre (i + 1 ) n (sublist ((i + 1 )) (n) (pts_l)) )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (((Znth i pts_l __default_Point).(x) ) = ((Znth i pts_l __default_Point).(x) )) ” 
  &&  “ (((Znth i pts_l __default_Point).(y) ) = ((Znth i pts_l __default_Point).(y) )) ” 
  &&  “ (((Znth pivot_idx pts_l __default_Point).(x) ) = ((Znth pivot_idx pts_l __default_Point).(x) )) ” 
  &&  “ (((Znth pivot_idx pts_l __default_Point).(y) ) = ((Znth pivot_idx pts_l __default_Point).(y) )) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
.

Definition sort_and_build_hull_entail_wit_4_1 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (n: Z) (i: Z) (pivot_idx: Z) (ax: Z) (ay: Z) (bx: Z) (b_y_val: Z) (retval: Z)  __default_Point ,
  “ (retval < 0) ” 
  &&  “ (retval = (point_cmp_leftdown ((point_mk (ax) (ay))) ((point_mk (bx) (b_y_val))))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (ax = ((Znth i pts_l __default_Point).(x) )) ” 
  &&  “ (ay = ((Znth i pts_l __default_Point).(y) )) ” 
  &&  “ (bx = ((Znth pivot_idx pts_l __default_Point).(x) )) ” 
  &&  “ (b_y_val = ((Znth pivot_idx pts_l __default_Point).(y) )) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n pts_l )
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
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
.

Definition sort_and_build_hull_entail_wit_4_2 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (n: Z) (i: Z) (pivot_idx: Z) (ax: Z) (ay: Z) (bx: Z) (b_y_val: Z) (retval: Z)  __default_Point ,
  “ (retval >= 0) ” 
  &&  “ (retval = (point_cmp_leftdown ((point_mk (ax) (ay))) ((point_mk (bx) (b_y_val))))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (ax = ((Znth i pts_l __default_Point).(x) )) ” 
  &&  “ (ay = ((Znth i pts_l __default_Point).(y) )) ” 
  &&  “ (bx = ((Znth pivot_idx pts_l __default_Point).(x) )) ” 
  &&  “ (b_y_val = ((Znth pivot_idx pts_l __default_Point).(y) )) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n pts_l )
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
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
.

Definition sort_and_build_hull_entail_wit_5 := 
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
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
.

Definition sort_and_build_hull_entail_wit_6_1 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (n: Z) (pivot_idx: Z)  __default_Point ,
  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (pivot_idx <> 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ”
  &&  (PointArray.full pts_pre n (point_swap (pts_l) (0) (pivot_idx)) )
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.undef_full hull_pre n )
|--
  EX (pts_pivot: (@list Point)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_pivot)) = n) ” 
  &&  “ (PointCoordsBound pts_pivot ) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  ((&(((pts_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth 0 pts_pivot __default_Point).(x) ))
  **  ((&(((pts_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth 0 pts_pivot __default_Point).(y) ))
  **  (PointArray.missing_i pts_pre 0 0 n pts_pivot )
  **  (PointArray.undef_full hull_pre n )
.

Definition sort_and_build_hull_entail_wit_6_2 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (n: Z) (pivot_idx: Z)  __default_Point ,
  “ (pivot_idx = 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  EX (pts_pivot: (@list Point)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_pivot)) = n) ” 
  &&  “ (PointCoordsBound pts_pivot ) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  ((&(((pts_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth 0 pts_pivot __default_Point).(x) ))
  **  ((&(((pts_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth 0 pts_pivot __default_Point).(y) ))
  **  (PointArray.missing_i pts_pre 0 0 n pts_pivot )
  **  (PointArray.undef_full hull_pre n )
.

Definition sort_and_build_hull_entail_wit_7 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot: (@list Point)) (n: Z) (pivot_idx: Z)  __default_Point ,
  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_pivot)) = n) ” 
  &&  “ (PointCoordsBound pts_pivot ) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  ((&(((pts_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "x")) # Int  |-> ((Znth 0 pts_pivot __default_Point).(x) ))
  **  ((&(((pts_pre + (0 * sizeof( "Point" ) ) ))  # "Point" ->ₛ "y")) # Int  |-> ((Znth 0 pts_pivot __default_Point).(y) ))
  **  (PointArray.missing_i pts_pre 0 0 n pts_pivot )
  **  (PointArray.undef_full hull_pre n )
|--
  EX (pts_pivot_2: (@list Point)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ (pts_pivot_2 = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_pivot_2)) = n) ” 
  &&  “ (PointCoordsBound pts_pivot_2 ) ” 
  &&  “ (((Znth 0 pts_pivot_2 __default_Point).(x) ) = ((Znth 0 pts_pivot __default_Point).(x) )) ” 
  &&  “ (((Znth 0 pts_pivot_2 __default_Point).(y) ) = ((Znth 0 pts_pivot __default_Point).(y) )) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n pts_pivot_2 )
  **  (PointArray.undef_full hull_pre n )
.

Definition sort_and_build_hull_entail_wit_8 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot_2: (@list Point)) (n: Z) (pivot_idx: Z) (gx: Z) (gy: Z)  __default_Point ,
  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ (pts_pivot_2 = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_pivot_2)) = n) ” 
  &&  “ (PointCoordsBound pts_pivot_2 ) ” 
  &&  “ (((Znth 0 pts_pivot_2 __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_pivot_2 __default_Point).(y) ) = gy) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.full pts_pre n pts_pivot_2 )
  **  (PointArray.undef_full hull_pre n )
|--
  EX (pts_pivot: (@list Point)) ,
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_pivot)) = n) ” 
  &&  “ (PointCoordsBound pts_pivot ) ” 
  &&  “ (((Znth 0 pts_pivot __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_pivot __default_Point).(y) ) = gy) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.full pts_pre n pts_pivot )
  **  (PointArray.undef_full hull_pre n )
.

Definition sort_and_build_hull_entail_wit_9 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot_2: (@list Point)) (n: Z) (pivot_idx: Z) (gx: Z) (gy: Z) (pts_out: (@list Point))  __default_Point ,
  “ ((Zlength (pts_out)) = n) ” 
  &&  “ (PointCoordsBound pts_out ) ” 
  &&  “ (PointPermutation pts_pivot_2 pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_pivot_2 pts_out 1 (n - 1 ) ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_out 1 (n - 1 ) ) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ (pts_pivot_2 = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_pivot_2)) = n) ” 
  &&  “ (PointCoordsBound pts_pivot_2 ) ” 
  &&  “ (((Znth 0 pts_pivot_2 __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_pivot_2 __default_Point).(y) ) = gy) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  (PointArray.full pts_pre n pts_out )
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.undef_full hull_pre n )
|--
  EX (pts_sorted: (@list Point))  (pts_pivot: (@list Point)) ,
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_sorted)) = n) ” 
  &&  “ (PointCoordsBound pts_sorted ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSameOutsideRange pts_pivot pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(y) ) = gy) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.full pts_pre n pts_sorted )
  **  (PointArray.undef_full hull_pre n )
.

Definition sort_and_build_hull_entail_wit_10 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot_2: (@list Point)) (pts_sorted_2: (@list Point)) (n: Z) (pivot_idx: Z) (gy: Z) (gx: Z)  __default_Point ,
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (pts_pivot_2 = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_sorted_2)) = n) ” 
  &&  “ (PointCoordsBound pts_sorted_2 ) ” 
  &&  “ (PointPermutation pts_pivot_2 pts_sorted_2 ) ” 
  &&  “ (PointSameOutsideRange pts_pivot_2 pts_sorted_2 1 (n - 1 ) ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted_2 1 (n - 1 ) ) ” 
  &&  “ (((Znth 0 pts_sorted_2 __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_sorted_2 __default_Point).(y) ) = gy) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.full pts_pre n pts_sorted_2 )
  **  (PointArray.undef_full hull_pre n )
|--
  EX (pts_cur: (@list Point))  (pts_sorted: (@list Point))  (pts_pivot: (@list Point)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= n) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < n) ” 
  &&  “ ((n - 1 ) = (n - 1 )) ” 
  &&  “ (1 <= ((n - 1 ) + 1 )) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_sorted)) = n) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (PointCoordsBound pts_sorted ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (PointTailReverseState pts_sorted pts_cur n 1 (n - 1 ) ) ” 
  &&  “ (((Znth 0 pts_cur __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_cur __default_Point).(y) ) = gy) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.full pts_pre n pts_cur )
  **  (PointArray.undef_full hull_pre n )
.

Definition sort_and_build_hull_entail_wit_11 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (gx: Z) (gy: Z) (pts_cur_2: (@list Point)) (pts_sorted_2: (@list Point)) (pivot_idx: Z) (pts_pivot_2: (@list Point)) (rev_j: Z) (rev_i: Z) (n: Z)  __default_Point ,
  “ ((Zlength (pts_cur_2)) = n) ” 
  &&  “ (rev_i < rev_j) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= rev_i) ” 
  &&  “ (rev_i <= n) ” 
  &&  “ (0 <= rev_j) ” 
  &&  “ (rev_j < n) ” 
  &&  “ (rev_j = (n - rev_i )) ” 
  &&  “ (rev_i <= (rev_j + 1 )) ” 
  &&  “ (pts_pivot_2 = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_sorted_2)) = n) ” 
  &&  “ ((Zlength (pts_cur_2)) = n) ” 
  &&  “ (PointCoordsBound pts_sorted_2 ) ” 
  &&  “ (PointCoordsBound pts_cur_2 ) ” 
  &&  “ (PointPermutation pts_pivot_2 pts_sorted_2 ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted_2 1 (n - 1 ) ) ” 
  &&  “ (PointTailReverseState pts_sorted_2 pts_cur_2 n rev_i rev_j ) ” 
  &&  “ (((Znth 0 pts_cur_2 __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_cur_2 __default_Point).(y) ) = gy) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  (PointArray.full pts_pre n (point_swap (pts_cur_2) (rev_i) (rev_j)) )
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.undef_full hull_pre n )
|--
  EX (pts_cur: (@list Point))  (pts_sorted: (@list Point))  (pts_pivot: (@list Point)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= (rev_i + 1 )) ” 
  &&  “ ((rev_i + 1 ) <= n) ” 
  &&  “ (0 <= (rev_j - 1 )) ” 
  &&  “ ((rev_j - 1 ) < n) ” 
  &&  “ ((rev_j - 1 ) = (n - (rev_i + 1 ) )) ” 
  &&  “ ((rev_i + 1 ) <= ((rev_j - 1 ) + 1 )) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_sorted)) = n) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (PointCoordsBound pts_sorted ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (PointTailReverseState pts_sorted pts_cur n (rev_i + 1 ) (rev_j - 1 ) ) ” 
  &&  “ (((Znth 0 pts_cur __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_cur __default_Point).(y) ) = gy) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.full pts_pre n pts_cur )
  **  (PointArray.undef_full hull_pre n )
.

Definition sort_and_build_hull_entail_wit_12 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (gx: Z) (gy: Z) (pts_cur: (@list Point)) (pts_sorted_2: (@list Point)) (pivot_idx: Z) (pts_pivot_2: (@list Point)) (rev_j: Z) (rev_i: Z) (n: Z)  __default_Point ,
  “ (rev_i >= rev_j) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= rev_i) ” 
  &&  “ (rev_i <= n) ” 
  &&  “ (0 <= rev_j) ” 
  &&  “ (rev_j < n) ” 
  &&  “ (rev_j = (n - rev_i )) ” 
  &&  “ (rev_i <= (rev_j + 1 )) ” 
  &&  “ (pts_pivot_2 = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_sorted_2)) = n) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (PointCoordsBound pts_sorted_2 ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointPermutation pts_pivot_2 pts_sorted_2 ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted_2 1 (n - 1 ) ) ” 
  &&  “ (PointTailReverseState pts_sorted_2 pts_cur n rev_i rev_j ) ” 
  &&  “ (((Znth 0 pts_cur __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_cur __default_Point).(y) ) = gy) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.full pts_pre n pts_cur )
  **  (PointArray.undef_full hull_pre n )
|--
  EX (pts_sorted: (@list Point))  (tail_rev: (@list Point))  (pts_rev: (@list Point))  (pts_pivot: (@list Point))  (pivot0: Point) ,
  “ ((pts_pre + (1 * sizeof( "Point" ) ) ) = (pts_pre + sizeof( "Point" ) )) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < INT_MAX) ” 
  &&  “ (pivot0 = (point_mk (gx) (gy))) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_rev)) = n) ” 
  &&  “ ((Zlength (tail_rev)) = (n - 1 )) ” 
  &&  “ (tail_rev = (sublist (1) (n) (pts_rev))) ” 
  &&  “ (PointCoordsBound pts_rev ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (PointTailReverseState pts_sorted pts_rev n rev_i rev_j ) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ” 
  &&  “ (((Znth 0 pts_rev __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_rev __default_Point).(y) ) = gy) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.seg pts_pre 0 1 (cons ((point_mk (gx) (gy))) (nil)) )
  **  (PointArray.full (pts_pre + (1 * sizeof( "Point" ) ) ) (n - 1 ) tail_rev )
  **  (PointArray.undef_full hull_pre ((n - 1 ) + 1 ) )
.

Definition sort_and_build_hull_return_wit_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot: (@list Point)) (pts_sorted: (@list Point)) (pts_rev: (@list Point)) (tail_rev: (@list Point)) (pivot0: Point) (tail: Z) (n: Z) (gy: Z) (gx: Z) (pivot_idx: Z) (rev_j: Z) (rev_i: Z) (retval: Z)  __default_Point ,
  “ (retval = (Zlength ((final_hull (pivot0) ((rev (tail_rev))))))) ” 
  &&  “ (is_convex_hull (rev (tail_rev)) (final_hull (pivot0) ((rev (tail_rev)))) ) ” 
  &&  “ (tail = (pts_pre + sizeof( "Point" ) )) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < INT_MAX) ” 
  &&  “ (pivot0 = (point_mk (gx) (gy))) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_rev)) = n) ” 
  &&  “ ((Zlength (tail_rev)) = (n - 1 )) ” 
  &&  “ (tail_rev = (sublist (1) (n) (pts_rev))) ” 
  &&  “ (PointCoordsBound pts_rev ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (PointTailReverseState pts_sorted pts_rev n rev_i rev_j ) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ” 
  &&  “ (((Znth 0 pts_rev __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_rev __default_Point).(y) ) = gy) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full tail (n - 1 ) tail_rev )
  **  (PointArray.seg hull_pre 0 retval (final_hull (pivot0) ((rev (tail_rev)))) )
  **  (PointArray.undef_seg hull_pre retval ((n - 1 ) + 1 ) )
  **  (PointArray.seg pts_pre 0 1 (cons ((point_mk (gx) (gy))) (nil)) )
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

Definition sort_and_build_hull_partial_solve_wit_1 := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (n: Z) (i: Z) (pivot_idx: Z) (ax: Z) (ay: Z) (bx: Z) (b_y_val: Z)  __default_Point ,
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (ax = ((Znth i pts_l __default_Point).(x) )) ” 
  &&  “ (ay = ((Znth i pts_l __default_Point).(y) )) ” 
  &&  “ (bx = ((Znth pivot_idx pts_l __default_Point).(x) )) ” 
  &&  “ (b_y_val = ((Znth pivot_idx pts_l __default_Point).(y) )) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < i) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (ax = ((Znth i pts_l __default_Point).(x) )) ” 
  &&  “ (ay = ((Znth i pts_l __default_Point).(y) )) ” 
  &&  “ (bx = ((Znth pivot_idx pts_l __default_Point).(x) )) ” 
  &&  “ (b_y_val = ((Znth pivot_idx pts_l __default_Point).(y) )) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
.

Definition sort_and_build_hull_partial_solve_wit_2_pure := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (n: Z) (pivot_idx: Z) ,
  “ (pivot_idx <> 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ”
  &&  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
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

Definition sort_and_build_hull_partial_solve_wit_2_aux := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (n: Z) (pivot_idx: Z) ,
  “ (pivot_idx <> 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n pts_l )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= 0) ” 
  &&  “ (0 < n) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ (0 <> pivot_idx) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (pivot_idx <> 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ ((Zlength (pts_l)) = n) ” 
  &&  “ (PointCoordsBound pts_l ) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ”
  &&  (PointArray.full pts_pre n pts_l )
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |->_)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |->_)
  **  (PointArray.undef_full hull_pre n )
.

Definition sort_and_build_hull_partial_solve_wit_2 := sort_and_build_hull_partial_solve_wit_2_pure -> sort_and_build_hull_partial_solve_wit_2_aux.

Definition sort_and_build_hull_partial_solve_wit_3_pure := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot: (@list Point)) (n: Z) (pivot_idx: Z) (gx: Z) (gy: Z)  __default_Point ,
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_pivot)) = n) ” 
  &&  “ (PointCoordsBound pts_pivot ) ” 
  &&  “ (((Znth 0 pts_pivot __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_pivot __default_Point).(y) ) = gy) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.full pts_pre n pts_pivot )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((-1) <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < n) ” 
  &&  “ ((Zlength (pts_pivot)) = n) ” 
  &&  “ (PointCoordsBound pts_pivot ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
.

Definition sort_and_build_hull_partial_solve_wit_3_aux := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot: (@list Point)) (n: Z) (pivot_idx: Z) (gx: Z) (gy: Z)  __default_Point ,
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_pivot)) = n) ” 
  &&  “ (PointCoordsBound pts_pivot ) ” 
  &&  “ (((Znth 0 pts_pivot __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_pivot __default_Point).(y) ) = gy) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.full pts_pre n pts_pivot )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((-1) <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < n) ” 
  &&  “ ((Zlength (pts_pivot)) = n) ” 
  &&  “ (PointCoordsBound pts_pivot ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= pivot_idx) ” 
  &&  “ (pivot_idx < n) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_pivot)) = n) ” 
  &&  “ (PointCoordsBound pts_pivot ) ” 
  &&  “ (((Znth 0 pts_pivot __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_pivot __default_Point).(y) ) = gy) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  (PointArray.full pts_pre n pts_pivot )
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.undef_full hull_pre n )
.

Definition sort_and_build_hull_partial_solve_wit_3 := sort_and_build_hull_partial_solve_wit_3_pure -> sort_and_build_hull_partial_solve_wit_3_aux.

Definition sort_and_build_hull_partial_solve_wit_4_pure := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (gx: Z) (gy: Z) (pts_cur: (@list Point)) (pts_sorted: (@list Point)) (pivot_idx: Z) (pts_pivot: (@list Point)) (rev_j: Z) (rev_i: Z) (n: Z)  __default_Point ,
  “ (rev_i < rev_j) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= rev_i) ” 
  &&  “ (rev_i <= n) ” 
  &&  “ (0 <= rev_j) ” 
  &&  “ (rev_j < n) ” 
  &&  “ (rev_j = (n - rev_i )) ” 
  &&  “ (rev_i <= (rev_j + 1 )) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_sorted)) = n) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (PointCoordsBound pts_sorted ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (PointTailReverseState pts_sorted pts_cur n rev_i rev_j ) ” 
  &&  “ (((Znth 0 pts_cur __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_cur __default_Point).(y) ) = gy) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "rev_i" ) )) # Int  |-> rev_i)
  **  ((( &( "rev_j" ) )) # Int  |-> rev_j)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.full pts_pre n pts_cur )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= rev_i) ” 
  &&  “ (rev_i < n) ” 
  &&  “ (0 <= rev_j) ” 
  &&  “ (rev_j < n) ” 
  &&  “ (rev_i <> rev_j) ” 
  &&  “ ((Zlength (pts_cur)) = n) ”
.

Definition sort_and_build_hull_partial_solve_wit_4_aux := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (gx: Z) (gy: Z) (pts_cur: (@list Point)) (pts_sorted: (@list Point)) (pivot_idx: Z) (pts_pivot: (@list Point)) (rev_j: Z) (rev_i: Z) (n: Z)  __default_Point ,
  “ (rev_i < rev_j) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= rev_i) ” 
  &&  “ (rev_i <= n) ” 
  &&  “ (0 <= rev_j) ” 
  &&  “ (rev_j < n) ” 
  &&  “ (rev_j = (n - rev_i )) ” 
  &&  “ (rev_i <= (rev_j + 1 )) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_sorted)) = n) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (PointCoordsBound pts_sorted ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (PointTailReverseState pts_sorted pts_cur n rev_i rev_j ) ” 
  &&  “ (((Znth 0 pts_cur __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_cur __default_Point).(y) ) = gy) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.full pts_pre n pts_cur )
  **  (PointArray.undef_full hull_pre n )
|--
  “ (0 <= rev_i) ” 
  &&  “ (rev_i < n) ” 
  &&  “ (0 <= rev_j) ” 
  &&  “ (rev_j < n) ” 
  &&  “ (rev_i <> rev_j) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (rev_i < rev_j) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (1 <= rev_i) ” 
  &&  “ (rev_i <= n) ” 
  &&  “ (0 <= rev_j) ” 
  &&  “ (rev_j < n) ” 
  &&  “ (rev_j = (n - rev_i )) ” 
  &&  “ (rev_i <= (rev_j + 1 )) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_sorted)) = n) ” 
  &&  “ ((Zlength (pts_cur)) = n) ” 
  &&  “ (PointCoordsBound pts_sorted ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (PointTailReverseState pts_sorted pts_cur n rev_i rev_j ) ” 
  &&  “ (((Znth 0 pts_cur __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_cur __default_Point).(y) ) = gy) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ”
  &&  (PointArray.full pts_pre n pts_cur )
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> gy)
  **  (PointArray.undef_full hull_pre n )
.

Definition sort_and_build_hull_partial_solve_wit_4 := sort_and_build_hull_partial_solve_wit_4_pure -> sort_and_build_hull_partial_solve_wit_4_aux.

Definition sort_and_build_hull_partial_solve_wit_5_pure := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot: (@list Point)) (pts_sorted: (@list Point)) (pts_rev: (@list Point)) (tail_rev: (@list Point)) (pivot0: Point) (tail: Z) (n: Z) (gy: Z) (gx: Z) (pivot_idx: Z) (rev_j: Z) (rev_i: Z)  __default_Point ,
  “ (tail = (pts_pre + sizeof( "Point" ) )) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < INT_MAX) ” 
  &&  “ (pivot0 = (point_mk (gx) (gy))) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_rev)) = n) ” 
  &&  “ ((Zlength (tail_rev)) = (n - 1 )) ” 
  &&  “ (tail_rev = (sublist (1) (n) (pts_rev))) ” 
  &&  “ (PointCoordsBound pts_rev ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (PointTailReverseState pts_sorted pts_rev n rev_i rev_j ) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ” 
  &&  “ (((Znth 0 pts_rev __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_rev __default_Point).(y) ) = gy) ”
  &&  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "tail" ) )) # Ptr  |-> tail)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  ((( &( "rev_j" ) )) # Int  |-> rev_j)
  **  ((( &( "rev_i" ) )) # Int  |-> rev_i)
  **  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.seg pts_pre 0 1 (cons ((point_mk (gx) (gy))) (nil)) )
  **  (PointArray.full tail (n - 1 ) tail_rev )
  **  (PointArray.undef_full hull_pre ((n - 1 ) + 1 ) )
|--
  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < INT_MAX) ” 
  &&  “ ((n - 1 ) = (Zlength (tail_rev))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ” 
  &&  “ (((Zlength (pts_rev)) - 1 ) = (Zlength ((sublist (1) (n) (pts_rev))))) ”
.

Definition sort_and_build_hull_partial_solve_wit_5_aux := 
forall (hull_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_pivot: (@list Point)) (pts_sorted: (@list Point)) (pts_rev: (@list Point)) (tail_rev: (@list Point)) (pivot0: Point) (tail: Z) (n: Z) (gy: Z) (gx: Z) (pivot_idx: Z) (rev_j: Z) (rev_i: Z)  __default_Point ,
  “ (tail = (pts_pre + sizeof( "Point" ) )) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < INT_MAX) ” 
  &&  “ (pivot0 = (point_mk (gx) (gy))) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_rev)) = n) ” 
  &&  “ ((Zlength (tail_rev)) = (n - 1 )) ” 
  &&  “ (tail_rev = (sublist (1) (n) (pts_rev))) ” 
  &&  “ (PointCoordsBound pts_rev ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (PointTailReverseState pts_sorted pts_rev n rev_i rev_j ) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ” 
  &&  “ (((Znth 0 pts_rev __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_rev __default_Point).(y) ) = gy) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.seg pts_pre 0 1 (cons ((point_mk (gx) (gy))) (nil)) )
  **  (PointArray.full tail (n - 1 ) tail_rev )
  **  (PointArray.undef_full hull_pre ((n - 1 ) + 1 ) )
|--
  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < INT_MAX) ” 
  &&  “ ((n - 1 ) = (Zlength (tail_rev))) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ” 
  &&  “ (((Zlength (pts_rev)) - 1 ) = (Zlength ((sublist (1) (n) (pts_rev))))) ” 
  &&  “ (tail = (pts_pre + sizeof( "Point" ) )) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < INT_MAX) ” 
  &&  “ (pivot0 = (point_mk (gx) (gy))) ” 
  &&  “ (pts_pivot = (point_swap (pts_l) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_rev)) = n) ” 
  &&  “ ((Zlength (tail_rev)) = (n - 1 )) ” 
  &&  “ (tail_rev = (sublist (1) (n) (pts_rev))) ” 
  &&  “ (PointCoordsBound pts_rev ) ” 
  &&  “ (PointPermutation pts_pivot pts_sorted ) ” 
  &&  “ (PointSortedRange_Point (point_mk (gx) (gy)) pts_sorted 1 (n - 1 ) ) ” 
  &&  “ (PointTailReverseState pts_sorted pts_rev n rev_i rev_j ) ” 
  &&  “ (sort pivot0 (rev (tail_rev)) ) ” 
  &&  “ (((Znth 0 pts_rev __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_rev __default_Point).(y) ) = gy) ”
  &&  ((&(( &( "g_pivot" ) )->ₛ "x")) # Int  |-> (pivot0.(x) ))
  **  ((&(( &( "g_pivot" ) )->ₛ "y")) # Int  |-> (pivot0.(y) ))
  **  (PointArray.full tail (n - 1 ) tail_rev )
  **  (PointArray.undef_full hull_pre ((n - 1 ) + 1 ) )
  **  (PointArray.seg pts_pre 0 1 (cons ((point_mk (gx) (gy))) (nil)) )
.

Definition sort_and_build_hull_partial_solve_wit_5 := sort_and_build_hull_partial_solve_wit_5_pure -> sort_and_build_hull_partial_solve_wit_5_aux.

Module Type VC_Correct.

Include point_array_Strategy_Correct.

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
Axiom proof_of_build_hull_from_sorted_tail_entail_wit_1 : build_hull_from_sorted_tail_entail_wit_1.
Axiom proof_of_build_hull_from_sorted_tail_entail_wit_2 : build_hull_from_sorted_tail_entail_wit_2.
Axiom proof_of_build_hull_from_sorted_tail_entail_wit_3 : build_hull_from_sorted_tail_entail_wit_3.
Axiom proof_of_build_hull_from_sorted_tail_entail_wit_4 : build_hull_from_sorted_tail_entail_wit_4.
Axiom proof_of_build_hull_from_sorted_tail_entail_wit_5 : build_hull_from_sorted_tail_entail_wit_5.
Axiom proof_of_build_hull_from_sorted_tail_entail_wit_6 : build_hull_from_sorted_tail_entail_wit_6.
Axiom proof_of_build_hull_from_sorted_tail_entail_wit_7 : build_hull_from_sorted_tail_entail_wit_7.
Axiom proof_of_build_hull_from_sorted_tail_entail_wit_8 : build_hull_from_sorted_tail_entail_wit_8.
Axiom proof_of_build_hull_from_sorted_tail_entail_wit_9_1 : build_hull_from_sorted_tail_entail_wit_9_1.
Axiom proof_of_build_hull_from_sorted_tail_entail_wit_9_2 : build_hull_from_sorted_tail_entail_wit_9_2.
Axiom proof_of_build_hull_from_sorted_tail_entail_wit_10 : build_hull_from_sorted_tail_entail_wit_10.
Axiom proof_of_build_hull_from_sorted_tail_entail_wit_11 : build_hull_from_sorted_tail_entail_wit_11.
Axiom proof_of_build_hull_from_sorted_tail_entail_wit_12 : build_hull_from_sorted_tail_entail_wit_12.
Axiom proof_of_build_hull_from_sorted_tail_entail_wit_13 : build_hull_from_sorted_tail_entail_wit_13.
Axiom proof_of_build_hull_from_sorted_tail_entail_wit_14 : build_hull_from_sorted_tail_entail_wit_14.
Axiom proof_of_build_hull_from_sorted_tail_return_wit_1 : build_hull_from_sorted_tail_return_wit_1.
Axiom proof_of_build_hull_from_sorted_tail_partial_solve_wit_1_pure : build_hull_from_sorted_tail_partial_solve_wit_1_pure.
Axiom proof_of_build_hull_from_sorted_tail_partial_solve_wit_1 : build_hull_from_sorted_tail_partial_solve_wit_1.
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
Axiom proof_of_sort_and_build_hull_safety_wit_1 : sort_and_build_hull_safety_wit_1.
Axiom proof_of_sort_and_build_hull_safety_wit_2 : sort_and_build_hull_safety_wit_2.
Axiom proof_of_sort_and_build_hull_safety_wit_3 : sort_and_build_hull_safety_wit_3.
Axiom proof_of_sort_and_build_hull_safety_wit_4 : sort_and_build_hull_safety_wit_4.
Axiom proof_of_sort_and_build_hull_safety_wit_5 : sort_and_build_hull_safety_wit_5.
Axiom proof_of_sort_and_build_hull_safety_wit_6 : sort_and_build_hull_safety_wit_6.
Axiom proof_of_sort_and_build_hull_safety_wit_7 : sort_and_build_hull_safety_wit_7.
Axiom proof_of_sort_and_build_hull_safety_wit_8 : sort_and_build_hull_safety_wit_8.
Axiom proof_of_sort_and_build_hull_safety_wit_9 : sort_and_build_hull_safety_wit_9.
Axiom proof_of_sort_and_build_hull_safety_wit_10 : sort_and_build_hull_safety_wit_10.
Axiom proof_of_sort_and_build_hull_safety_wit_11 : sort_and_build_hull_safety_wit_11.
Axiom proof_of_sort_and_build_hull_safety_wit_12 : sort_and_build_hull_safety_wit_12.
Axiom proof_of_sort_and_build_hull_safety_wit_13 : sort_and_build_hull_safety_wit_13.
Axiom proof_of_sort_and_build_hull_safety_wit_14 : sort_and_build_hull_safety_wit_14.
Axiom proof_of_sort_and_build_hull_safety_wit_15 : sort_and_build_hull_safety_wit_15.
Axiom proof_of_sort_and_build_hull_safety_wit_16 : sort_and_build_hull_safety_wit_16.
Axiom proof_of_sort_and_build_hull_safety_wit_17 : sort_and_build_hull_safety_wit_17.
Axiom proof_of_sort_and_build_hull_safety_wit_18 : sort_and_build_hull_safety_wit_18.
Axiom proof_of_sort_and_build_hull_safety_wit_19 : sort_and_build_hull_safety_wit_19.
Axiom proof_of_sort_and_build_hull_safety_wit_20 : sort_and_build_hull_safety_wit_20.
Axiom proof_of_sort_and_build_hull_entail_wit_1 : sort_and_build_hull_entail_wit_1.
Axiom proof_of_sort_and_build_hull_entail_wit_2 : sort_and_build_hull_entail_wit_2.
Axiom proof_of_sort_and_build_hull_entail_wit_3 : sort_and_build_hull_entail_wit_3.
Axiom proof_of_sort_and_build_hull_entail_wit_4_1 : sort_and_build_hull_entail_wit_4_1.
Axiom proof_of_sort_and_build_hull_entail_wit_4_2 : sort_and_build_hull_entail_wit_4_2.
Axiom proof_of_sort_and_build_hull_entail_wit_5 : sort_and_build_hull_entail_wit_5.
Axiom proof_of_sort_and_build_hull_entail_wit_6_1 : sort_and_build_hull_entail_wit_6_1.
Axiom proof_of_sort_and_build_hull_entail_wit_6_2 : sort_and_build_hull_entail_wit_6_2.
Axiom proof_of_sort_and_build_hull_entail_wit_7 : sort_and_build_hull_entail_wit_7.
Axiom proof_of_sort_and_build_hull_entail_wit_8 : sort_and_build_hull_entail_wit_8.
Axiom proof_of_sort_and_build_hull_entail_wit_9 : sort_and_build_hull_entail_wit_9.
Axiom proof_of_sort_and_build_hull_entail_wit_10 : sort_and_build_hull_entail_wit_10.
Axiom proof_of_sort_and_build_hull_entail_wit_11 : sort_and_build_hull_entail_wit_11.
Axiom proof_of_sort_and_build_hull_entail_wit_12 : sort_and_build_hull_entail_wit_12.
Axiom proof_of_sort_and_build_hull_return_wit_1 : sort_and_build_hull_return_wit_1.
Axiom proof_of_sort_and_build_hull_partial_solve_wit_1 : sort_and_build_hull_partial_solve_wit_1.
Axiom proof_of_sort_and_build_hull_partial_solve_wit_2_pure : sort_and_build_hull_partial_solve_wit_2_pure.
Axiom proof_of_sort_and_build_hull_partial_solve_wit_2 : sort_and_build_hull_partial_solve_wit_2.
Axiom proof_of_sort_and_build_hull_partial_solve_wit_3_pure : sort_and_build_hull_partial_solve_wit_3_pure.
Axiom proof_of_sort_and_build_hull_partial_solve_wit_3 : sort_and_build_hull_partial_solve_wit_3.
Axiom proof_of_sort_and_build_hull_partial_solve_wit_4_pure : sort_and_build_hull_partial_solve_wit_4_pure.
Axiom proof_of_sort_and_build_hull_partial_solve_wit_4 : sort_and_build_hull_partial_solve_wit_4.
Axiom proof_of_sort_and_build_hull_partial_solve_wit_5_pure : sort_and_build_hull_partial_solve_wit_5_pure.
Axiom proof_of_sort_and_build_hull_partial_solve_wit_5 : sort_and_build_hull_partial_solve_wit_5.

End VC_Correct.
