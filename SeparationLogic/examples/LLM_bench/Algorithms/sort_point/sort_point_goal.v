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
Require Import SimpleC.EE.LLM_bench.Algorithms.sort_point.sort_point_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function cmp_polar_values -----*)

Definition cmp_polar_values_safety_wit_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "adx" ) )) # Int  |->_)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ ((a_x_pre - gx_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a_x_pre - gx_pre )) ”
.

Definition cmp_polar_values_safety_wit_2 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "ady" ) )) # Int  |->_)
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ ((a_y_pre - gy_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a_y_pre - gy_pre )) ”
.

Definition cmp_polar_values_safety_wit_3 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bdx" ) )) # Int  |->_)
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ ((b_x_pre - gx_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_x_pre - gx_pre )) ”
.

Definition cmp_polar_values_safety_wit_4 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bdy" ) )) # Int  |->_)
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ ((b_y_pre - gy_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_y_pre - gy_pre )) ”
.

Definition cmp_polar_values_safety_wit_5 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "cr" ) )) # Int  |->_)
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) )) ”
.

Definition cmp_polar_values_safety_wit_6 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "cr" ) )) # Int  |->_)
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) )) ”
.

Definition cmp_polar_values_safety_wit_7 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "cr" ) )) # Int  |->_)
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) )) ”
.

Definition cmp_polar_values_safety_wit_8 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "da" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) )) ”
.

Definition cmp_polar_values_safety_wit_9 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "da" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) )) ”
.

Definition cmp_polar_values_safety_wit_10 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "da" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) )) ”
.

Definition cmp_polar_values_safety_wit_11 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "db" ) )) # Int  |->_)
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ ((((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ”
.

Definition cmp_polar_values_safety_wit_12 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "db" ) )) # Int  |->_)
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) )) ”
.

Definition cmp_polar_values_safety_wit_13 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "db" ) )) # Int  |->_)
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) )) ”
.

Definition cmp_polar_values_safety_wit_14 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "ah" ) )) # Int  |->_)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_15 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_16 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_17 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_18 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_19 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_20 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |->_)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_21 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |->_)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_22 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |->_)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_23 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |->_)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_24 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_25 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_26 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_27 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_28 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_29 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_30 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_31 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_32 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_33 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_34 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_35 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_36 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_37 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_38 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_39 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_40 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_41 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_42 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_43 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_44 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_45 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_46 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_47 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_48 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_49 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_50 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_51 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_52 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_53 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_54 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_55 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_56 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_57 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_58 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_59 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_60 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_61 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_62 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_63 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_64 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_65 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_66 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_67 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_68 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_69 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_70 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_71 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_72 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_73 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_74 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_75 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_76 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_77 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_78 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_79 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_80 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_81 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_82 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_83 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_84 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_85 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_86 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_87 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_88 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) < 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_89 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) < 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_90 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) < 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_91 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) < 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_92 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) < 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_93 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) < 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_94 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) < 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_95 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) < 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_96 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_97 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_98 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_99 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_100 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_101 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_102 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_103 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_104 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_105 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_106 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_107 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_108 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_109 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_110 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_111 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_112 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) > (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_113 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) > (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_114 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) > (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_115 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) > (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_116 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) > (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_117 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) > (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_118 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) > (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_119 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) > (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_120 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_121 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_122 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_123 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_124 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_125 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_126 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_127 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_128 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_129 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_130 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_131 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_132 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_133 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_134 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_135 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_136 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre > b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_137 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre > b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_138 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre > b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_139 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre > b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_140 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre > b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_141 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre > b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_142 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre > b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_143 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre > b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_144 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre < b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ False ”
.

Definition cmp_polar_values_safety_wit_145 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ False ”
.

Definition cmp_polar_values_safety_wit_146 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre < b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ False ”
.

Definition cmp_polar_values_safety_wit_147 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre < b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ False ”
.

Definition cmp_polar_values_safety_wit_148 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre < b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ False ”
.

Definition cmp_polar_values_safety_wit_149 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ False ”
.

Definition cmp_polar_values_safety_wit_150 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre < b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_151 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre < b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_152 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre < b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_153 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre < b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_values_safety_wit_154 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre < b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_155 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre < b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_156 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre < b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_157 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre < b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_158 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre > b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ False ”
.

Definition cmp_polar_values_safety_wit_159 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre <= b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ False ”
.

Definition cmp_polar_values_safety_wit_160 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre > b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ False ”
.

Definition cmp_polar_values_safety_wit_161 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre <= b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ False ”
.

Definition cmp_polar_values_safety_wit_162 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre > b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_163 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre > b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_164 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre > b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_165 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre > b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_values_safety_wit_166 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre <= b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_167 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre <= b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 0)
  **  ((( &( "ah" ) )) # Int  |-> 0)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_168 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre <= b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_safety_wit_169 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre <= b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  ((( &( "bh" ) )) # Int  |-> 1)
  **  ((( &( "ah" ) )) # Int  |-> 1)
  **  ((( &( "db" ) )) # Int  |-> (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) ))
  **  ((( &( "da" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ))
  **  ((( &( "cr" ) )) # Int  |-> (((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ))
  **  ((( &( "bdy" ) )) # Int  |-> (b_y_pre - gy_pre ))
  **  ((( &( "bdx" ) )) # Int  |-> (b_x_pre - gx_pre ))
  **  ((( &( "ady" ) )) # Int  |-> (a_y_pre - gy_pre ))
  **  ((( &( "adx" ) )) # Int  |-> (a_x_pre - gx_pre ))
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_values_return_wit_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre <= b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 0 ) ” 
  &&  “ ((-1) <= 0) ” 
  &&  “ (0 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_2 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre <= b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 0 ) ” 
  &&  “ ((-1) <= 0) ” 
  &&  “ (0 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_3 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre <= b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 0 ) ” 
  &&  “ ((-1) <= 0) ” 
  &&  “ (0 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_4 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre <= b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 0 ) ” 
  &&  “ ((-1) <= 0) ” 
  &&  “ (0 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_5 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre > b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_6 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre > b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_7 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre > b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_8 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre > b_y_pre) ” 
  &&  “ (a_y_pre >= b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_9 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre < b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_10 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre < b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_11 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre < b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_12 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_y_pre < b_y_pre) ” 
  &&  “ (a_x_pre <= b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_13 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre > b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_14 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre > b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_15 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre > b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_16 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre > b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_17 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre > b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_18 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre > b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_19 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre > b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_20 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre > b_x_pre) ” 
  &&  “ (a_x_pre >= b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_21 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_22 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_23 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_24 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_25 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_26 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_27 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_28 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ (a_x_pre < b_x_pre) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) <= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_29 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) > (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_30 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) > (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_31 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) > (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_32 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) > (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_33 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) > (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_34 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) > (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_35 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) > (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_36 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) > (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) >= (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_37 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_38 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_39 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_40 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_41 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_42 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_43 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_44 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (a_x_pre - gx_pre ) ) + ((a_y_pre - gy_pre ) * (a_y_pre - gy_pre ) ) ) < (((b_x_pre - gx_pre ) * (b_x_pre - gx_pre ) ) + ((b_y_pre - gy_pre ) * (b_y_pre - gy_pre ) ) )) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) >= 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_45 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) < 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_46 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) < 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_47 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) < 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_48 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) < 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_49 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) < 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_50 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) < 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_51 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) < 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_52 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) < 0) ” 
  &&  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) <= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_53 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_54 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_55 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_56 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_57 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_58 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_59 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_60 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((((a_x_pre - gx_pre ) * (b_y_pre - gy_pre ) ) - ((a_y_pre - gy_pre ) * (b_x_pre - gx_pre ) ) ) > 0) ” 
  &&  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_61 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_62 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) > 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_63 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_64 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) < 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1 ) ” 
  &&  “ ((-1) <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_65 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_66 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_y_pre - gy_pre ) <> 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_67 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_x_pre - gx_pre ) >= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) = 0) ” 
  &&  “ ((a_y_pre - gy_pre ) <= 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

Definition cmp_polar_values_return_wit_68 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gy_pre: Z) (gx_pre: Z) ,
  “ ((b_x_pre - gx_pre ) < 0) ” 
  &&  “ ((b_y_pre - gy_pre ) = 0) ” 
  &&  “ ((b_y_pre - gy_pre ) <= 0) ” 
  &&  “ ((a_y_pre - gy_pre ) > 0) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds a_x_pre ) ” 
  &&  “ (CoordInBounds a_y_pre ) ” 
  &&  “ (CoordInBounds b_x_pre ) ” 
  &&  “ (CoordInBounds b_y_pre ) ”
  &&  emp
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 1) ”
  &&  emp
.

(*----- Function swap_points -----*)

Definition swap_points_safety_wit_1 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((( &( "tmp_x" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  (IntArray.full coords_pre (2 * n_pre ) flat )
|--
  “ ((2 * i_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i_pre )) ”
.

Definition swap_points_safety_wit_2 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((( &( "tmp_x" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  (IntArray.full coords_pre (2 * n_pre ) flat )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition swap_points_safety_wit_3 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((( &( "tmp_y" ) )) # Int  |->_)
  **  (IntArray.full coords_pre (2 * n_pre ) flat )
  **  ((( &( "tmp_x" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ (((2 * i_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * i_pre ) + 1 )) ”
.

Definition swap_points_safety_wit_4 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((( &( "tmp_y" ) )) # Int  |->_)
  **  (IntArray.full coords_pre (2 * n_pre ) flat )
  **  ((( &( "tmp_x" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ ((2 * i_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i_pre )) ”
.

Definition swap_points_safety_wit_5 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((( &( "tmp_y" ) )) # Int  |->_)
  **  (IntArray.full coords_pre (2 * n_pre ) flat )
  **  ((( &( "tmp_x" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition swap_points_safety_wit_6 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  ((( &( "tmp_y" ) )) # Int  |->_)
  **  (IntArray.full coords_pre (2 * n_pre ) flat )
  **  ((( &( "tmp_x" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition swap_points_safety_wit_7 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat )
  **  ((( &( "tmp_y" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_x" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ ((2 * i_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i_pre )) ”
.

Definition swap_points_safety_wit_8 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat )
  **  ((( &( "tmp_y" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_x" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition swap_points_safety_wit_9 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat )
  **  ((( &( "tmp_y" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_x" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ ((2 * j_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * j_pre )) ”
.

Definition swap_points_safety_wit_10 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat )
  **  ((( &( "tmp_y" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_x" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition swap_points_safety_wit_11 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
  **  ((( &( "tmp_y" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_x" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ (((2 * i_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * i_pre ) + 1 )) ”
.

Definition swap_points_safety_wit_12 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
  **  ((( &( "tmp_y" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_x" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ ((2 * i_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i_pre )) ”
.

Definition swap_points_safety_wit_13 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
  **  ((( &( "tmp_y" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_x" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition swap_points_safety_wit_14 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
  **  ((( &( "tmp_y" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_x" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition swap_points_safety_wit_15 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
  **  ((( &( "tmp_y" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_x" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ (((2 * j_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * j_pre ) + 1 )) ”
.

Definition swap_points_safety_wit_16 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
  **  ((( &( "tmp_y" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_x" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ ((2 * j_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * j_pre )) ”
.

Definition swap_points_safety_wit_17 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
  **  ((( &( "tmp_y" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_x" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition swap_points_safety_wit_18 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
  **  ((( &( "tmp_y" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_x" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition swap_points_safety_wit_19 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))) )
  **  ((( &( "tmp_y" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_x" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ ((2 * j_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * j_pre )) ”
.

Definition swap_points_safety_wit_20 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))) )
  **  ((( &( "tmp_y" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_x" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition swap_points_safety_wit_21 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (replace_Znth ((2 * j_pre )) ((Znth (2 * i_pre ) flat 0)) ((replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))))) )
  **  ((( &( "tmp_y" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_x" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ (((2 * j_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * j_pre ) + 1 )) ”
.

Definition swap_points_safety_wit_22 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (replace_Znth ((2 * j_pre )) ((Znth (2 * i_pre ) flat 0)) ((replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))))) )
  **  ((( &( "tmp_y" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_x" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ ((2 * j_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * j_pre )) ”
.

Definition swap_points_safety_wit_23 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (replace_Znth ((2 * j_pre )) ((Znth (2 * i_pre ) flat 0)) ((replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))))) )
  **  ((( &( "tmp_y" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_x" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition swap_points_safety_wit_24 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (replace_Znth ((2 * j_pre )) ((Znth (2 * i_pre ) flat 0)) ((replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))))) )
  **  ((( &( "tmp_y" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_x" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition swap_points_return_wit_1 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (replace_Znth (((2 * j_pre ) + 1 )) ((Znth ((2 * i_pre ) + 1 ) flat 0)) ((replace_Znth ((2 * j_pre )) ((Znth (2 * i_pre ) flat 0)) ((replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))))))) )
|--
  “ (FlatPoints (point_swap_flat (flat) (i_pre) (j_pre)) (point_swap_points (pts_l) (i_pre) (j_pre)) ) ” 
  &&  “ (PointPermutation pts_l (point_swap_points (pts_l) (i_pre) (j_pre)) ) ” 
  &&  “ (PointCoordsBound (point_swap_points (pts_l) (i_pre) (j_pre)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (point_swap_flat (flat) (i_pre) (j_pre)) )
.

Definition swap_points_partial_solve_wit_1 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (((coords_pre + ((2 * i_pre ) * sizeof(INT) ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  (IntArray.missing_i coords_pre (2 * i_pre ) 0 (2 * n_pre ) flat )
.

Definition swap_points_partial_solve_wit_2 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (((coords_pre + (((2 * i_pre ) + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  (IntArray.missing_i coords_pre ((2 * i_pre ) + 1 ) 0 (2 * n_pre ) flat )
.

Definition swap_points_partial_solve_wit_3 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (((coords_pre + ((2 * j_pre ) * sizeof(INT) ) )) # Int  |-> (Znth (2 * j_pre ) flat 0))
  **  (IntArray.missing_i coords_pre (2 * j_pre ) 0 (2 * n_pre ) flat )
.

Definition swap_points_partial_solve_wit_4 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (((coords_pre + ((2 * i_pre ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i coords_pre (2 * i_pre ) 0 (2 * n_pre ) flat )
.

Definition swap_points_partial_solve_wit_5 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (((coords_pre + (((2 * j_pre ) + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0))
  **  (IntArray.missing_i coords_pre ((2 * j_pre ) + 1 ) 0 (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
.

Definition swap_points_partial_solve_wit_6 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (((coords_pre + (((2 * i_pre ) + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i coords_pre ((2 * i_pre ) + 1 ) 0 (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
.

Definition swap_points_partial_solve_wit_7 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))) )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (((coords_pre + ((2 * j_pre ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i coords_pre (2 * j_pre ) 0 (2 * n_pre ) (replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))) )
.

Definition swap_points_partial_solve_wit_8 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (replace_Znth ((2 * j_pre )) ((Znth (2 * i_pre ) flat 0)) ((replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))))) )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound pts_l ) ”
  &&  (((coords_pre + (((2 * j_pre ) + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i coords_pre ((2 * j_pre ) + 1 ) 0 (2 * n_pre ) (replace_Znth ((2 * j_pre )) ((Znth (2 * i_pre ) flat 0)) ((replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))))) )
.

(*----- Function partition_points -----*)

Definition partition_points_safety_wit_1 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  ((( &( "pivot_x" ) )) # Int  |->_)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  (IntArray.full coords_pre (2 * n_pre ) flat )
|--
  “ ((2 * high_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * high_pre )) ”
.

Definition partition_points_safety_wit_2 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  ((( &( "pivot_x" ) )) # Int  |->_)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  (IntArray.full coords_pre (2 * n_pre ) flat )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition partition_points_safety_wit_3 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  ((( &( "pivot_y" ) )) # Int  |->_)
  **  (IntArray.full coords_pre (2 * n_pre ) flat )
  **  ((( &( "pivot_x" ) )) # Int  |-> (Znth (2 * high_pre ) flat 0))
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ (((2 * high_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * high_pre ) + 1 )) ”
.

Definition partition_points_safety_wit_4 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  ((( &( "pivot_y" ) )) # Int  |->_)
  **  (IntArray.full coords_pre (2 * n_pre ) flat )
  **  ((( &( "pivot_x" ) )) # Int  |-> (Znth (2 * high_pre ) flat 0))
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ ((2 * high_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * high_pre )) ”
.

Definition partition_points_safety_wit_5 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  ((( &( "pivot_y" ) )) # Int  |->_)
  **  (IntArray.full coords_pre (2 * n_pre ) flat )
  **  ((( &( "pivot_x" ) )) # Int  |-> (Znth (2 * high_pre ) flat 0))
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition partition_points_safety_wit_6 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  ((( &( "pivot_y" ) )) # Int  |->_)
  **  (IntArray.full coords_pre (2 * n_pre ) flat )
  **  ((( &( "pivot_x" ) )) # Int  |-> (Znth (2 * high_pre ) flat 0))
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_points_safety_wit_7 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full coords_pre (2 * n_pre ) flat )
  **  ((( &( "pivot_y" ) )) # Int  |-> (Znth ((2 * high_pre ) + 1 ) flat 0))
  **  ((( &( "pivot_x" ) )) # Int  |-> (Znth (2 * high_pre ) flat 0))
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ ((low_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (low_pre - 1 )) ”
.

Definition partition_points_safety_wit_8 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full coords_pre (2 * n_pre ) flat )
  **  ((( &( "pivot_y" ) )) # Int  |-> (Znth ((2 * high_pre ) + 1 ) flat 0))
  **  ((( &( "pivot_x" ) )) # Int  |-> (Znth (2 * high_pre ) flat 0))
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_points_safety_wit_9 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur: (@list point)) (j: Z) (i: Z) ,
  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "ax" ) )) # Int  |->_)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
|--
  “ ((2 * j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * j )) ”
.

Definition partition_points_safety_wit_10 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur: (@list point)) (j: Z) (i: Z) ,
  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "ax" ) )) # Int  |->_)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition partition_points_safety_wit_11 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur: (@list point)) (j: Z) (i: Z) ,
  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "ay" ) )) # Int  |->_)
  **  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
  **  ((( &( "ax" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
|--
  “ (((2 * j ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * j ) + 1 )) ”
.

Definition partition_points_safety_wit_12 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur: (@list point)) (j: Z) (i: Z) ,
  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "ay" ) )) # Int  |->_)
  **  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
  **  ((( &( "ax" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
|--
  “ ((2 * j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * j )) ”
.

Definition partition_points_safety_wit_13 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur: (@list point)) (j: Z) (i: Z) ,
  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "ay" ) )) # Int  |->_)
  **  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
  **  ((( &( "ax" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition partition_points_safety_wit_14 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur: (@list point)) (j: Z) (i: Z) ,
  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "ay" ) )) # Int  |->_)
  **  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
  **  ((( &( "ax" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_points_safety_wit_15 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur: (@list point)) (j: Z) (i: Z) (retval: Z) ,
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point ((Znth (2 * j ) flat_cur 0)) ((Znth ((2 * j ) + 1 ) flat_cur 0))) (mk_point (pivot_x) (pivot_y)) retval ) ” 
  &&  “ ((-1) <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "c" ) )) # Int  |-> retval)
  **  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
  **  ((( &( "ay" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "ax" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition partition_points_safety_wit_16 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur: (@list point)) (j: Z) (i: Z) (retval: Z) ,
  “ (retval <= 0) ” 
  &&  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point ((Znth (2 * j ) flat_cur 0)) ((Znth ((2 * j ) + 1 ) flat_cur 0))) (mk_point (pivot_x) (pivot_y)) retval ) ” 
  &&  “ ((-1) <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "c" ) )) # Int  |-> retval)
  **  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
  **  ((( &( "ay" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "ax" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_points_safety_wit_17 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur: (@list point)) (j: Z) (i: Z) (retval: Z) ,
  “ (retval > 0) ” 
  &&  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point ((Znth (2 * j ) flat_cur 0)) ((Znth ((2 * j ) + 1 ) flat_cur 0))) (mk_point (pivot_x) (pivot_y)) retval ) ” 
  &&  “ ((-1) <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition partition_points_safety_wit_18 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur: (@list point)) (j: Z) (i: Z) (retval: Z) ,
  “ (FlatPoints (point_swap_flat (flat_cur) ((i + 1 )) (j)) (point_swap_points (pts_cur) ((i + 1 )) (j)) ) ” 
  &&  “ (PointPermutation pts_cur (point_swap_points (pts_cur) ((i + 1 )) (j)) ) ” 
  &&  “ (PointCoordsBound (point_swap_points (pts_cur) ((i + 1 )) (j)) ) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point ((Znth (2 * j ) flat_cur 0)) ((Znth ((2 * j ) + 1 ) flat_cur 0))) (mk_point (pivot_x) (pivot_y)) retval ) ” 
  &&  “ ((-1) <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (point_swap_flat (flat_cur) ((i + 1 )) (j)) )
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition partition_points_safety_wit_19 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur: (@list point)) (j: Z) (i: Z) ,
  “ (j >= high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_points_safety_wit_20 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur: (@list point)) (j: Z) (i: Z) ,
  “ (j >= high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_points_safety_wit_21 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur: (@list point)) (j: Z) (i: Z) ,
  “ (FlatPoints (point_swap_flat (flat_cur) ((i + 1 )) (high_pre)) (point_swap_points (pts_cur) ((i + 1 )) (high_pre)) ) ” 
  &&  “ (PointPermutation pts_cur (point_swap_points (pts_cur) ((i + 1 )) (high_pre)) ) ” 
  &&  “ (PointCoordsBound (point_swap_points (pts_cur) ((i + 1 )) (high_pre)) ) ” 
  &&  “ (j >= high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (point_swap_flat (flat_cur) ((i + 1 )) (high_pre)) )
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_points_safety_wit_22 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur: (@list point)) (j: Z) (i: Z) ,
  “ (FlatPoints (point_swap_flat (flat_cur) ((i + 1 )) (high_pre)) (point_swap_points (pts_cur) ((i + 1 )) (high_pre)) ) ” 
  &&  “ (PointPermutation pts_cur (point_swap_points (pts_cur) ((i + 1 )) (high_pre)) ) ” 
  &&  “ (PointCoordsBound (point_swap_points (pts_cur) ((i + 1 )) (high_pre)) ) ” 
  &&  “ (j >= high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (point_swap_flat (flat_cur) ((i + 1 )) (high_pre)) )
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_points_entail_wit_1 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat )
|--
  EX (flat_cur: (@list Z))  (pts_cur: (@list point)) ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= (low_pre - 1 )) ” 
  &&  “ ((low_pre - 1 ) < low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point ((Znth (2 * high_pre ) flat 0)) ((Znth ((2 * high_pre ) + 1 ) flat 0))) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point ((Znth (2 * high_pre ) flat 0)) ((Znth ((2 * high_pre ) + 1 ) flat 0))) (low_pre - 1 ) low_pre ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
.

Definition partition_points_entail_wit_2_1 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur_2: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur_2: (@list point)) (j: Z) (i: Z) (retval: Z) ,
  “ (FlatPoints (point_swap_flat (flat_cur_2) ((i + 1 )) (j)) (point_swap_points (pts_cur_2) ((i + 1 )) (j)) ) ” 
  &&  “ (PointPermutation pts_cur_2 (point_swap_points (pts_cur_2) ((i + 1 )) (j)) ) ” 
  &&  “ (PointCoordsBound (point_swap_points (pts_cur_2) ((i + 1 )) (j)) ) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point ((Znth (2 * j ) flat_cur_2 0)) ((Znth ((2 * j ) + 1 ) flat_cur_2 0))) (mk_point (pivot_x) (pivot_y)) retval ) ” 
  &&  “ ((-1) <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur_2)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur_2) (default_point))) ” 
  &&  “ (FlatPoints flat_cur_2 pts_cur_2 ) ” 
  &&  “ (PointCoordsBound pts_cur_2 ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur_2)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (point_swap_flat (flat_cur_2) ((i + 1 )) (j)) )
|--
  EX (flat_cur: (@list Z))  (pts_cur: (@list point)) ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < (j + 1 )) ” 
  &&  “ ((j + 1 ) <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) (i + 1 ) (j + 1 ) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
.

Definition partition_points_entail_wit_2_2 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur_2: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur_2: (@list point)) (j: Z) (i: Z) (retval: Z) ,
  “ (retval > 0) ” 
  &&  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point ((Znth (2 * j ) flat_cur_2 0)) ((Znth ((2 * j ) + 1 ) flat_cur_2 0))) (mk_point (pivot_x) (pivot_y)) retval ) ” 
  &&  “ ((-1) <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur_2)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur_2) (default_point))) ” 
  &&  “ (FlatPoints flat_cur_2 pts_cur_2 ) ” 
  &&  “ (PointCoordsBound pts_cur_2 ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur_2)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_cur_2 )
|--
  EX (flat_cur: (@list Z))  (pts_cur: (@list point)) ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < (j + 1 )) ” 
  &&  “ ((j + 1 ) <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i (j + 1 ) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
.

Definition partition_points_return_wit_1 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur: (@list point)) (j: Z) (i: Z) ,
  “ (FlatPoints (point_swap_flat (flat_cur) ((i + 1 )) (high_pre)) (point_swap_points (pts_cur) ((i + 1 )) (high_pre)) ) ” 
  &&  “ (PointPermutation pts_cur (point_swap_points (pts_cur) ((i + 1 )) (high_pre)) ) ” 
  &&  “ (PointCoordsBound (point_swap_points (pts_cur) ((i + 1 )) (high_pre)) ) ” 
  &&  “ (j >= high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) (point_swap_flat (flat_cur) ((i + 1 )) (high_pre)) )
|--
  EX (flat_out: (@list Z))  (pts_out: (@list point)) ,
  “ (low_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= high_pre) ” 
  &&  “ (FlatPoints flat_out pts_out ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out)) ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out low_pre high_pre ) ” 
  &&  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out low_pre high_pre (i + 1 ) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out )
.

Definition partition_points_partial_solve_wit_1 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat )
|--
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (((coords_pre + ((2 * high_pre ) * sizeof(INT) ) )) # Int  |-> (Znth (2 * high_pre ) flat 0))
  **  (IntArray.missing_i coords_pre (2 * high_pre ) 0 (2 * n_pre ) flat )
.

Definition partition_points_partial_solve_wit_2 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat )
|--
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (((coords_pre + (((2 * high_pre ) + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth ((2 * high_pre ) + 1 ) flat 0))
  **  (IntArray.missing_i coords_pre ((2 * high_pre ) + 1 ) 0 (2 * n_pre ) flat )
.

Definition partition_points_partial_solve_wit_3 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur: (@list point)) (j: Z) (i: Z) ,
  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
|--
  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  (((coords_pre + ((2 * j ) * sizeof(INT) ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  (IntArray.missing_i coords_pre (2 * j ) 0 (2 * n_pre ) flat_cur )
.

Definition partition_points_partial_solve_wit_4 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur: (@list point)) (j: Z) (i: Z) ,
  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
|--
  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  (((coords_pre + (((2 * j ) + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  (IntArray.missing_i coords_pre ((2 * j ) + 1 ) 0 (2 * n_pre ) flat_cur )
.

Definition partition_points_partial_solve_wit_5_pure := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur: (@list point)) (j: Z) (i: Z) ,
  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "c" ) )) # Int  |->_)
  **  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
  **  ((( &( "ay" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "ax" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
|--
  “ (CoordInBounds pivot_y ) ” 
  &&  “ (CoordInBounds pivot_x ) ” 
  &&  “ (CoordInBounds (Znth ((2 * j ) + 1 ) flat_cur 0) ) ” 
  &&  “ (CoordInBounds (Znth (2 * j ) flat_cur 0) ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds gx_pre ) ”
.

Definition partition_points_partial_solve_wit_5_aux := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur: (@list point)) (j: Z) (i: Z) ,
  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
|--
  “ (CoordInBounds pivot_y ) ” 
  &&  “ (CoordInBounds pivot_x ) ” 
  &&  “ (CoordInBounds (Znth ((2 * j ) + 1 ) flat_cur 0) ) ” 
  &&  “ (CoordInBounds (Znth (2 * j ) flat_cur 0) ) ” 
  &&  “ (CoordInBounds gy_pre ) ” 
  &&  “ (CoordInBounds gx_pre ) ” 
  &&  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
.

Definition partition_points_partial_solve_wit_5 := partition_points_partial_solve_wit_5_pure -> partition_points_partial_solve_wit_5_aux.

Definition partition_points_partial_solve_wit_6_pure := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur: (@list point)) (j: Z) (i: Z) (retval: Z) ,
  “ (retval <= 0) ” 
  &&  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point ((Znth (2 * j ) flat_cur 0)) ((Znth ((2 * j ) + 1 ) flat_cur 0))) (mk_point (pivot_x) (pivot_y)) retval ) ” 
  &&  “ ((-1) <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "c" ) )) # Int  |-> retval)
  **  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
  **  ((( &( "ay" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "ax" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ”
.

Definition partition_points_partial_solve_wit_6_aux := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur: (@list point)) (j: Z) (i: Z) (retval: Z) ,
  “ (retval <= 0) ” 
  &&  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point ((Znth (2 * j ) flat_cur 0)) ((Znth ((2 * j ) + 1 ) flat_cur 0))) (mk_point (pivot_x) (pivot_y)) retval ) ” 
  &&  “ ((-1) <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point ((Znth (2 * j ) flat_cur 0)) ((Znth ((2 * j ) + 1 ) flat_cur 0))) (mk_point (pivot_x) (pivot_y)) retval ) ” 
  &&  “ ((-1) <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
.

Definition partition_points_partial_solve_wit_6 := partition_points_partial_solve_wit_6_pure -> partition_points_partial_solve_wit_6_aux.

Definition partition_points_partial_solve_wit_7_pure := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur: (@list point)) (j: Z) (i: Z) ,
  “ (j >= high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ”
.

Definition partition_points_partial_solve_wit_7_aux := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (coords_pre: Z) (pts_l: (@list point)) (flat_cur: (@list Z)) (pivot_x: Z) (pivot_y: Z) (pts_cur: (@list point)) (j: Z) (i: Z) ,
  “ (j >= high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (j >= high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” 
  &&  “ (FlatPoints flat_cur pts_cur ) ” 
  &&  “ (PointCoordsBound pts_cur ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_cur)) ) ” 
  &&  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_cur )
.

Definition partition_points_partial_solve_wit_7 := partition_points_partial_solve_wit_7_pure -> partition_points_partial_solve_wit_7_aux.

(*----- Function quicksort_points_range -----*)

Definition quicksort_points_range_safety_wit_1 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (coords_pre: Z) (flat: (@list Z)) (pts_l: (@list point)) (flat_out: (@list Z)) (pts_out: (@list point)) (retval: Z) ,
  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (FlatPoints flat_out pts_out ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out)) ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
|--
  “ ((retval - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - 1 )) ”
.

Definition quicksort_points_range_safety_wit_2 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (coords_pre: Z) (flat: (@list Z)) (pts_l: (@list point)) (flat_out: (@list Z)) (pts_out: (@list point)) (retval: Z) ,
  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (FlatPoints flat_out pts_out ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out)) ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_points_range_safety_wit_3 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (coords_pre: Z) (flat: (@list Z)) (pts_l: (@list point)) (flat_out: (@list Z)) (pts_out: (@list point)) (retval: Z) ,
  “ (retval >= right_pre) ” 
  &&  “ (retval <= left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (FlatPoints flat_out pts_out ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out)) ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
|--
  “ False ”
.

Definition quicksort_points_range_safety_wit_4 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (coords_pre: Z) (flat: (@list Z)) (pts_l: (@list point)) (flat_out: (@list Z)) (pts_out: (@list point)) (retval: Z) (flat_out_2: (@list Z)) (pts_out_2: (@list point)) ,
  “ (retval < right_pre) ” 
  &&  “ (FlatPoints flat_out_2 pts_out_2 ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out_2)) ) ” 
  &&  “ (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out pts_out_2 left_pre (retval - 1 ) ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (FlatPoints flat_out pts_out ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out)) ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out_2 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition quicksort_points_range_safety_wit_5 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (coords_pre: Z) (flat: (@list Z)) (pts_l: (@list point)) (flat_out: (@list Z)) (pts_out: (@list point)) (retval: Z) (flat_out_2: (@list Z)) (pts_out_2: (@list point)) ,
  “ (retval < right_pre) ” 
  &&  “ (FlatPoints flat_out_2 pts_out_2 ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out_2)) ) ” 
  &&  “ (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out pts_out_2 left_pre (retval - 1 ) ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (FlatPoints flat_out pts_out ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out)) ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out_2 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_points_range_safety_wit_6 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (coords_pre: Z) (flat: (@list Z)) (pts_l: (@list point)) (flat_out: (@list Z)) (pts_out: (@list point)) (retval: Z) ,
  “ (retval < right_pre) ” 
  &&  “ (retval <= left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (FlatPoints flat_out pts_out ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out)) ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition quicksort_points_range_safety_wit_7 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (coords_pre: Z) (flat: (@list Z)) (pts_l: (@list point)) (flat_out: (@list Z)) (pts_out: (@list point)) (retval: Z) ,
  “ (retval < right_pre) ” 
  &&  “ (retval <= left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (FlatPoints flat_out pts_out ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out)) ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_points_range_entail_wit_1 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (coords_pre: Z) (flat: (@list Z)) ,
  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat )
|--
  EX (pts_l: (@list point)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat )
.

Definition quicksort_points_range_return_wit_1 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (coords_pre: Z) (flat: (@list Z)) (pts_l: (@list point)) (flat_out_2: (@list Z)) (pts_out_2: (@list point)) (retval: Z) (flat_out_3: (@list Z)) (pts_out_3: (@list point)) (flat_out_4: (@list Z)) (pts_out_4: (@list point)) ,
  “ (FlatPoints flat_out_4 pts_out_4 ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out_4)) ) ” 
  &&  “ (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_3 pts_out_4 (retval + 1 ) right_pre ) ” 
  &&  “ (retval < right_pre) ” 
  &&  “ (FlatPoints flat_out_3 pts_out_3 ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out_3)) ) ” 
  &&  “ (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_3 left_pre (retval - 1 ) ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (FlatPoints flat_out_2 pts_out_2 ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out_2)) ) ” 
  &&  “ (PointPermutation pts_l pts_out_2 ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out_2 left_pre right_pre ) ” 
  &&  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out_4 )
|--
  EX (flat_out: (@list Z))  (pts_out: (@list point)) ,
  “ (FlatPoints flat_out pts_out ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out)) ) ” 
  &&  “ (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat pts_out left_pre right_pre ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out )
.

Definition quicksort_points_range_return_wit_2 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (coords_pre: Z) (flat: (@list Z)) (pts_l: (@list point)) (flat_out_2: (@list Z)) (pts_out_2: (@list point)) (retval: Z) (flat_out_3: (@list Z)) (pts_out_3: (@list point)) ,
  “ (FlatPoints flat_out_3 pts_out_3 ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out_3)) ) ” 
  &&  “ (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_3 (retval + 1 ) right_pre ) ” 
  &&  “ (retval < right_pre) ” 
  &&  “ (retval <= left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (FlatPoints flat_out_2 pts_out_2 ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out_2)) ) ” 
  &&  “ (PointPermutation pts_l pts_out_2 ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out_2 left_pre right_pre ) ” 
  &&  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out_3 )
|--
  EX (flat_out: (@list Z))  (pts_out: (@list point)) ,
  “ (FlatPoints flat_out pts_out ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out)) ) ” 
  &&  “ (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat pts_out left_pre right_pre ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out )
.

Definition quicksort_points_range_return_wit_3 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (coords_pre: Z) (flat: (@list Z)) (pts_l: (@list point)) (flat_out_2: (@list Z)) (pts_out_2: (@list point)) (retval: Z) (flat_out_3: (@list Z)) (pts_out_3: (@list point)) ,
  “ (retval >= right_pre) ” 
  &&  “ (FlatPoints flat_out_3 pts_out_3 ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out_3)) ) ” 
  &&  “ (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_3 left_pre (retval - 1 ) ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (FlatPoints flat_out_2 pts_out_2 ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out_2)) ) ” 
  &&  “ (PointPermutation pts_l pts_out_2 ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out_2 left_pre right_pre ) ” 
  &&  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out_3 )
|--
  EX (flat_out: (@list Z))  (pts_out: (@list point)) ,
  “ (FlatPoints flat_out pts_out ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out)) ) ” 
  &&  “ (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat pts_out left_pre right_pre ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out )
.

Definition quicksort_points_range_return_wit_4 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (coords_pre: Z) (flat: (@list Z)) ,
  “ (left_pre >= right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat )
|--
  EX (flat_out: (@list Z))  (pts_out: (@list point)) ,
  “ (FlatPoints flat_out pts_out ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out)) ) ” 
  &&  “ (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat pts_out left_pre right_pre ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out )
.

Definition quicksort_points_range_partial_solve_wit_1_pure := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (coords_pre: Z) (flat: (@list Z)) (pts_l: (@list point)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  (IntArray.full coords_pre (2 * n_pre ) flat )
|--
  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
.

Definition quicksort_points_range_partial_solve_wit_1_aux := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (coords_pre: Z) (flat: (@list Z)) (pts_l: (@list point)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat )
|--
  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat )
.

Definition quicksort_points_range_partial_solve_wit_1 := quicksort_points_range_partial_solve_wit_1_pure -> quicksort_points_range_partial_solve_wit_1_aux.

Definition quicksort_points_range_partial_solve_wit_2_pure := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (coords_pre: Z) (flat: (@list Z)) (pts_l: (@list point)) (flat_out: (@list Z)) (pts_out: (@list point)) (retval: Z) ,
  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (FlatPoints flat_out pts_out ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out)) ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= (retval - 1 )) ” 
  &&  “ ((retval - 1 ) < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat_out n_pre ) ”
.

Definition quicksort_points_range_partial_solve_wit_2_aux := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (coords_pre: Z) (flat: (@list Z)) (pts_l: (@list point)) (flat_out: (@list Z)) (pts_out: (@list point)) (retval: Z) ,
  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (FlatPoints flat_out pts_out ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out)) ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= (retval - 1 )) ” 
  &&  “ ((retval - 1 ) < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat_out n_pre ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (FlatPoints flat_out pts_out ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out)) ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out )
.

Definition quicksort_points_range_partial_solve_wit_2 := quicksort_points_range_partial_solve_wit_2_pure -> quicksort_points_range_partial_solve_wit_2_aux.

Definition quicksort_points_range_partial_solve_wit_3_pure := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (coords_pre: Z) (flat: (@list Z)) (pts_l: (@list point)) (flat_out_2: (@list Z)) (pts_out: (@list point)) (retval: Z) (flat_out: (@list Z)) (pts_out_2: (@list point)) ,
  “ (retval < right_pre) ” 
  &&  “ (FlatPoints flat_out pts_out_2 ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out_2)) ) ” 
  &&  “ (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_2 left_pre (retval - 1 ) ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (FlatPoints flat_out_2 pts_out ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out)) ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat_out n_pre ) ”
.

Definition quicksort_points_range_partial_solve_wit_3_aux := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (coords_pre: Z) (flat: (@list Z)) (pts_l: (@list point)) (flat_out_2: (@list Z)) (pts_out: (@list point)) (retval: Z) (flat_out: (@list Z)) (pts_out_2: (@list point)) ,
  “ (retval < right_pre) ” 
  &&  “ (FlatPoints flat_out pts_out_2 ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out_2)) ) ” 
  &&  “ (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_2 left_pre (retval - 1 ) ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (FlatPoints flat_out_2 pts_out ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out)) ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat_out n_pre ) ” 
  &&  “ (retval < right_pre) ” 
  &&  “ (FlatPoints flat_out pts_out_2 ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out_2)) ) ” 
  &&  “ (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_2 left_pre (retval - 1 ) ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (FlatPoints flat_out_2 pts_out ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out)) ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out )
.

Definition quicksort_points_range_partial_solve_wit_3 := quicksort_points_range_partial_solve_wit_3_pure -> quicksort_points_range_partial_solve_wit_3_aux.

Definition quicksort_points_range_partial_solve_wit_4_pure := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (coords_pre: Z) (flat: (@list Z)) (pts_l: (@list point)) (flat_out: (@list Z)) (pts_out: (@list point)) (retval: Z) ,
  “ (retval < right_pre) ” 
  &&  “ (retval <= left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (FlatPoints flat_out pts_out ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out)) ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "coords" ) )) # Ptr  |-> coords_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat_out n_pre ) ”
.

Definition quicksort_points_range_partial_solve_wit_4_aux := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (coords_pre: Z) (flat: (@list Z)) (pts_l: (@list point)) (flat_out: (@list Z)) (pts_out: (@list point)) (retval: Z) ,
  “ (retval < right_pre) ” 
  &&  “ (retval <= left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (FlatPoints flat_out pts_out ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out)) ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat_out n_pre ) ” 
  &&  “ (retval < right_pre) ” 
  &&  “ (retval <= left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (FlatPoints flat_out pts_out ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_out)) ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre ) ” 
  &&  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx_pre) (gy_pre)) flat n_pre ) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx_pre) (gy_pre))) (pts_l)) ) ”
  &&  (IntArray.full coords_pre (2 * n_pre ) flat_out )
.

Definition quicksort_points_range_partial_solve_wit_4 := quicksort_points_range_partial_solve_wit_4_pure -> quicksort_points_range_partial_solve_wit_4_aux.

(*----- Function sort -----*)

Definition sort_safety_wit_1 := 
forall (n_pre: Z) (pts_pre: Z) (gy: Z) (gx: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx) (gy))) (pts_l)) ) ”
  &&  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "coords" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((&(( &( "gp" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "gp" ) )->ₛ "y")) # Int  |-> gy)
  **  (IntArray.full pts_pre (2 * n_pre ) flat )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition sort_safety_wit_2 := 
forall (n_pre: Z) (pts_pre: Z) (gy: Z) (gx: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx) (gy))) (pts_l)) ) ”
  &&  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "coords" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((&(( &( "gp" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "gp" ) )->ₛ "y")) # Int  |-> gy)
  **  (IntArray.full pts_pre (2 * n_pre ) flat )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_safety_wit_3 := 
forall (n_pre: Z) (pts_pre: Z) (gy: Z) (gx: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx) (gy))) (pts_l)) ) ”
  &&  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "coords" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((&(( &( "gp" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "gp" ) )->ₛ "y")) # Int  |-> gy)
  **  (IntArray.full pts_pre (2 * n_pre ) flat )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_return_wit_1 := 
forall (n_pre: Z) (pts_pre: Z) (gy: Z) (gx: Z) (pts_l: (@list point)) (flat: (@list Z)) (flat_out_2: (@list Z)) (pts_out_2: (@list point)) ,
  “ (FlatPoints flat_out_2 pts_out_2 ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx) (gy))) (pts_out_2)) ) ” 
  &&  “ (PointRangeSortResult (mk_point (gx) (gy)) flat pts_out_2 0 (n_pre - 1 ) ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx) (gy))) (pts_l)) ) ”
  &&  (IntArray.full pts_pre (2 * n_pre ) flat_out_2 )
  **  ((&(( &( "gp" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "gp" ) )->ₛ "y")) # Int  |-> gy)
|--
  EX (flat_out: (@list Z))  (pts_out: (@list point)) ,
  “ (FlatPoints flat_out pts_out ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx) (gy))) (pts_out)) ) ” 
  &&  “ (PointPermutation pts_l pts_out ) ” 
  &&  “ (PolarSorted (mk_point (gx) (gy)) pts_out ) ”
  &&  ((&(( &( "gp" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "gp" ) )->ₛ "y")) # Int  |-> gy)
  **  (IntArray.full pts_pre (2 * n_pre ) flat_out )
.

Definition sort_partial_solve_wit_1_pure := 
forall (n_pre: Z) (pts_pre: Z) (gy: Z) (gx: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx) (gy))) (pts_l)) ) ”
  &&  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "coords" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((&(( &( "gp" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "gp" ) )->ₛ "y")) # Int  |-> gy)
  **  (IntArray.full pts_pre (2 * n_pre ) flat )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((-1) <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx) (gy)) flat n_pre ) ”
.

Definition sort_partial_solve_wit_1_aux := 
forall (n_pre: Z) (pts_pre: Z) (gy: Z) (gx: Z) (pts_l: (@list point)) (flat: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx) (gy))) (pts_l)) ) ”
  &&  ((&(( &( "gp" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "gp" ) )->ₛ "y")) # Int  |-> gy)
  **  (IntArray.full pts_pre (2 * n_pre ) flat )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((-1) <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ (PointMemoryModel (mk_point (gx) (gy)) flat n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (FlatPoints flat pts_l ) ” 
  &&  “ (PointCoordsBound (cons ((mk_point (gx) (gy))) (pts_l)) ) ”
  &&  (IntArray.full pts_pre (2 * n_pre ) flat )
  **  ((&(( &( "gp" ) )->ₛ "x")) # Int  |-> gx)
  **  ((&(( &( "gp" ) )->ₛ "y")) # Int  |-> gy)
.

Definition sort_partial_solve_wit_1 := sort_partial_solve_wit_1_pure -> sort_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_cmp_polar_values_safety_wit_1 : cmp_polar_values_safety_wit_1.
Axiom proof_of_cmp_polar_values_safety_wit_2 : cmp_polar_values_safety_wit_2.
Axiom proof_of_cmp_polar_values_safety_wit_3 : cmp_polar_values_safety_wit_3.
Axiom proof_of_cmp_polar_values_safety_wit_4 : cmp_polar_values_safety_wit_4.
Axiom proof_of_cmp_polar_values_safety_wit_5 : cmp_polar_values_safety_wit_5.
Axiom proof_of_cmp_polar_values_safety_wit_6 : cmp_polar_values_safety_wit_6.
Axiom proof_of_cmp_polar_values_safety_wit_7 : cmp_polar_values_safety_wit_7.
Axiom proof_of_cmp_polar_values_safety_wit_8 : cmp_polar_values_safety_wit_8.
Axiom proof_of_cmp_polar_values_safety_wit_9 : cmp_polar_values_safety_wit_9.
Axiom proof_of_cmp_polar_values_safety_wit_10 : cmp_polar_values_safety_wit_10.
Axiom proof_of_cmp_polar_values_safety_wit_11 : cmp_polar_values_safety_wit_11.
Axiom proof_of_cmp_polar_values_safety_wit_12 : cmp_polar_values_safety_wit_12.
Axiom proof_of_cmp_polar_values_safety_wit_13 : cmp_polar_values_safety_wit_13.
Axiom proof_of_cmp_polar_values_safety_wit_14 : cmp_polar_values_safety_wit_14.
Axiom proof_of_cmp_polar_values_safety_wit_15 : cmp_polar_values_safety_wit_15.
Axiom proof_of_cmp_polar_values_safety_wit_16 : cmp_polar_values_safety_wit_16.
Axiom proof_of_cmp_polar_values_safety_wit_17 : cmp_polar_values_safety_wit_17.
Axiom proof_of_cmp_polar_values_safety_wit_18 : cmp_polar_values_safety_wit_18.
Axiom proof_of_cmp_polar_values_safety_wit_19 : cmp_polar_values_safety_wit_19.
Axiom proof_of_cmp_polar_values_safety_wit_20 : cmp_polar_values_safety_wit_20.
Axiom proof_of_cmp_polar_values_safety_wit_21 : cmp_polar_values_safety_wit_21.
Axiom proof_of_cmp_polar_values_safety_wit_22 : cmp_polar_values_safety_wit_22.
Axiom proof_of_cmp_polar_values_safety_wit_23 : cmp_polar_values_safety_wit_23.
Axiom proof_of_cmp_polar_values_safety_wit_24 : cmp_polar_values_safety_wit_24.
Axiom proof_of_cmp_polar_values_safety_wit_25 : cmp_polar_values_safety_wit_25.
Axiom proof_of_cmp_polar_values_safety_wit_26 : cmp_polar_values_safety_wit_26.
Axiom proof_of_cmp_polar_values_safety_wit_27 : cmp_polar_values_safety_wit_27.
Axiom proof_of_cmp_polar_values_safety_wit_28 : cmp_polar_values_safety_wit_28.
Axiom proof_of_cmp_polar_values_safety_wit_29 : cmp_polar_values_safety_wit_29.
Axiom proof_of_cmp_polar_values_safety_wit_30 : cmp_polar_values_safety_wit_30.
Axiom proof_of_cmp_polar_values_safety_wit_31 : cmp_polar_values_safety_wit_31.
Axiom proof_of_cmp_polar_values_safety_wit_32 : cmp_polar_values_safety_wit_32.
Axiom proof_of_cmp_polar_values_safety_wit_33 : cmp_polar_values_safety_wit_33.
Axiom proof_of_cmp_polar_values_safety_wit_34 : cmp_polar_values_safety_wit_34.
Axiom proof_of_cmp_polar_values_safety_wit_35 : cmp_polar_values_safety_wit_35.
Axiom proof_of_cmp_polar_values_safety_wit_36 : cmp_polar_values_safety_wit_36.
Axiom proof_of_cmp_polar_values_safety_wit_37 : cmp_polar_values_safety_wit_37.
Axiom proof_of_cmp_polar_values_safety_wit_38 : cmp_polar_values_safety_wit_38.
Axiom proof_of_cmp_polar_values_safety_wit_39 : cmp_polar_values_safety_wit_39.
Axiom proof_of_cmp_polar_values_safety_wit_40 : cmp_polar_values_safety_wit_40.
Axiom proof_of_cmp_polar_values_safety_wit_41 : cmp_polar_values_safety_wit_41.
Axiom proof_of_cmp_polar_values_safety_wit_42 : cmp_polar_values_safety_wit_42.
Axiom proof_of_cmp_polar_values_safety_wit_43 : cmp_polar_values_safety_wit_43.
Axiom proof_of_cmp_polar_values_safety_wit_44 : cmp_polar_values_safety_wit_44.
Axiom proof_of_cmp_polar_values_safety_wit_45 : cmp_polar_values_safety_wit_45.
Axiom proof_of_cmp_polar_values_safety_wit_46 : cmp_polar_values_safety_wit_46.
Axiom proof_of_cmp_polar_values_safety_wit_47 : cmp_polar_values_safety_wit_47.
Axiom proof_of_cmp_polar_values_safety_wit_48 : cmp_polar_values_safety_wit_48.
Axiom proof_of_cmp_polar_values_safety_wit_49 : cmp_polar_values_safety_wit_49.
Axiom proof_of_cmp_polar_values_safety_wit_50 : cmp_polar_values_safety_wit_50.
Axiom proof_of_cmp_polar_values_safety_wit_51 : cmp_polar_values_safety_wit_51.
Axiom proof_of_cmp_polar_values_safety_wit_52 : cmp_polar_values_safety_wit_52.
Axiom proof_of_cmp_polar_values_safety_wit_53 : cmp_polar_values_safety_wit_53.
Axiom proof_of_cmp_polar_values_safety_wit_54 : cmp_polar_values_safety_wit_54.
Axiom proof_of_cmp_polar_values_safety_wit_55 : cmp_polar_values_safety_wit_55.
Axiom proof_of_cmp_polar_values_safety_wit_56 : cmp_polar_values_safety_wit_56.
Axiom proof_of_cmp_polar_values_safety_wit_57 : cmp_polar_values_safety_wit_57.
Axiom proof_of_cmp_polar_values_safety_wit_58 : cmp_polar_values_safety_wit_58.
Axiom proof_of_cmp_polar_values_safety_wit_59 : cmp_polar_values_safety_wit_59.
Axiom proof_of_cmp_polar_values_safety_wit_60 : cmp_polar_values_safety_wit_60.
Axiom proof_of_cmp_polar_values_safety_wit_61 : cmp_polar_values_safety_wit_61.
Axiom proof_of_cmp_polar_values_safety_wit_62 : cmp_polar_values_safety_wit_62.
Axiom proof_of_cmp_polar_values_safety_wit_63 : cmp_polar_values_safety_wit_63.
Axiom proof_of_cmp_polar_values_safety_wit_64 : cmp_polar_values_safety_wit_64.
Axiom proof_of_cmp_polar_values_safety_wit_65 : cmp_polar_values_safety_wit_65.
Axiom proof_of_cmp_polar_values_safety_wit_66 : cmp_polar_values_safety_wit_66.
Axiom proof_of_cmp_polar_values_safety_wit_67 : cmp_polar_values_safety_wit_67.
Axiom proof_of_cmp_polar_values_safety_wit_68 : cmp_polar_values_safety_wit_68.
Axiom proof_of_cmp_polar_values_safety_wit_69 : cmp_polar_values_safety_wit_69.
Axiom proof_of_cmp_polar_values_safety_wit_70 : cmp_polar_values_safety_wit_70.
Axiom proof_of_cmp_polar_values_safety_wit_71 : cmp_polar_values_safety_wit_71.
Axiom proof_of_cmp_polar_values_safety_wit_72 : cmp_polar_values_safety_wit_72.
Axiom proof_of_cmp_polar_values_safety_wit_73 : cmp_polar_values_safety_wit_73.
Axiom proof_of_cmp_polar_values_safety_wit_74 : cmp_polar_values_safety_wit_74.
Axiom proof_of_cmp_polar_values_safety_wit_75 : cmp_polar_values_safety_wit_75.
Axiom proof_of_cmp_polar_values_safety_wit_76 : cmp_polar_values_safety_wit_76.
Axiom proof_of_cmp_polar_values_safety_wit_77 : cmp_polar_values_safety_wit_77.
Axiom proof_of_cmp_polar_values_safety_wit_78 : cmp_polar_values_safety_wit_78.
Axiom proof_of_cmp_polar_values_safety_wit_79 : cmp_polar_values_safety_wit_79.
Axiom proof_of_cmp_polar_values_safety_wit_80 : cmp_polar_values_safety_wit_80.
Axiom proof_of_cmp_polar_values_safety_wit_81 : cmp_polar_values_safety_wit_81.
Axiom proof_of_cmp_polar_values_safety_wit_82 : cmp_polar_values_safety_wit_82.
Axiom proof_of_cmp_polar_values_safety_wit_83 : cmp_polar_values_safety_wit_83.
Axiom proof_of_cmp_polar_values_safety_wit_84 : cmp_polar_values_safety_wit_84.
Axiom proof_of_cmp_polar_values_safety_wit_85 : cmp_polar_values_safety_wit_85.
Axiom proof_of_cmp_polar_values_safety_wit_86 : cmp_polar_values_safety_wit_86.
Axiom proof_of_cmp_polar_values_safety_wit_87 : cmp_polar_values_safety_wit_87.
Axiom proof_of_cmp_polar_values_safety_wit_88 : cmp_polar_values_safety_wit_88.
Axiom proof_of_cmp_polar_values_safety_wit_89 : cmp_polar_values_safety_wit_89.
Axiom proof_of_cmp_polar_values_safety_wit_90 : cmp_polar_values_safety_wit_90.
Axiom proof_of_cmp_polar_values_safety_wit_91 : cmp_polar_values_safety_wit_91.
Axiom proof_of_cmp_polar_values_safety_wit_92 : cmp_polar_values_safety_wit_92.
Axiom proof_of_cmp_polar_values_safety_wit_93 : cmp_polar_values_safety_wit_93.
Axiom proof_of_cmp_polar_values_safety_wit_94 : cmp_polar_values_safety_wit_94.
Axiom proof_of_cmp_polar_values_safety_wit_95 : cmp_polar_values_safety_wit_95.
Axiom proof_of_cmp_polar_values_safety_wit_96 : cmp_polar_values_safety_wit_96.
Axiom proof_of_cmp_polar_values_safety_wit_97 : cmp_polar_values_safety_wit_97.
Axiom proof_of_cmp_polar_values_safety_wit_98 : cmp_polar_values_safety_wit_98.
Axiom proof_of_cmp_polar_values_safety_wit_99 : cmp_polar_values_safety_wit_99.
Axiom proof_of_cmp_polar_values_safety_wit_100 : cmp_polar_values_safety_wit_100.
Axiom proof_of_cmp_polar_values_safety_wit_101 : cmp_polar_values_safety_wit_101.
Axiom proof_of_cmp_polar_values_safety_wit_102 : cmp_polar_values_safety_wit_102.
Axiom proof_of_cmp_polar_values_safety_wit_103 : cmp_polar_values_safety_wit_103.
Axiom proof_of_cmp_polar_values_safety_wit_104 : cmp_polar_values_safety_wit_104.
Axiom proof_of_cmp_polar_values_safety_wit_105 : cmp_polar_values_safety_wit_105.
Axiom proof_of_cmp_polar_values_safety_wit_106 : cmp_polar_values_safety_wit_106.
Axiom proof_of_cmp_polar_values_safety_wit_107 : cmp_polar_values_safety_wit_107.
Axiom proof_of_cmp_polar_values_safety_wit_108 : cmp_polar_values_safety_wit_108.
Axiom proof_of_cmp_polar_values_safety_wit_109 : cmp_polar_values_safety_wit_109.
Axiom proof_of_cmp_polar_values_safety_wit_110 : cmp_polar_values_safety_wit_110.
Axiom proof_of_cmp_polar_values_safety_wit_111 : cmp_polar_values_safety_wit_111.
Axiom proof_of_cmp_polar_values_safety_wit_112 : cmp_polar_values_safety_wit_112.
Axiom proof_of_cmp_polar_values_safety_wit_113 : cmp_polar_values_safety_wit_113.
Axiom proof_of_cmp_polar_values_safety_wit_114 : cmp_polar_values_safety_wit_114.
Axiom proof_of_cmp_polar_values_safety_wit_115 : cmp_polar_values_safety_wit_115.
Axiom proof_of_cmp_polar_values_safety_wit_116 : cmp_polar_values_safety_wit_116.
Axiom proof_of_cmp_polar_values_safety_wit_117 : cmp_polar_values_safety_wit_117.
Axiom proof_of_cmp_polar_values_safety_wit_118 : cmp_polar_values_safety_wit_118.
Axiom proof_of_cmp_polar_values_safety_wit_119 : cmp_polar_values_safety_wit_119.
Axiom proof_of_cmp_polar_values_safety_wit_120 : cmp_polar_values_safety_wit_120.
Axiom proof_of_cmp_polar_values_safety_wit_121 : cmp_polar_values_safety_wit_121.
Axiom proof_of_cmp_polar_values_safety_wit_122 : cmp_polar_values_safety_wit_122.
Axiom proof_of_cmp_polar_values_safety_wit_123 : cmp_polar_values_safety_wit_123.
Axiom proof_of_cmp_polar_values_safety_wit_124 : cmp_polar_values_safety_wit_124.
Axiom proof_of_cmp_polar_values_safety_wit_125 : cmp_polar_values_safety_wit_125.
Axiom proof_of_cmp_polar_values_safety_wit_126 : cmp_polar_values_safety_wit_126.
Axiom proof_of_cmp_polar_values_safety_wit_127 : cmp_polar_values_safety_wit_127.
Axiom proof_of_cmp_polar_values_safety_wit_128 : cmp_polar_values_safety_wit_128.
Axiom proof_of_cmp_polar_values_safety_wit_129 : cmp_polar_values_safety_wit_129.
Axiom proof_of_cmp_polar_values_safety_wit_130 : cmp_polar_values_safety_wit_130.
Axiom proof_of_cmp_polar_values_safety_wit_131 : cmp_polar_values_safety_wit_131.
Axiom proof_of_cmp_polar_values_safety_wit_132 : cmp_polar_values_safety_wit_132.
Axiom proof_of_cmp_polar_values_safety_wit_133 : cmp_polar_values_safety_wit_133.
Axiom proof_of_cmp_polar_values_safety_wit_134 : cmp_polar_values_safety_wit_134.
Axiom proof_of_cmp_polar_values_safety_wit_135 : cmp_polar_values_safety_wit_135.
Axiom proof_of_cmp_polar_values_safety_wit_136 : cmp_polar_values_safety_wit_136.
Axiom proof_of_cmp_polar_values_safety_wit_137 : cmp_polar_values_safety_wit_137.
Axiom proof_of_cmp_polar_values_safety_wit_138 : cmp_polar_values_safety_wit_138.
Axiom proof_of_cmp_polar_values_safety_wit_139 : cmp_polar_values_safety_wit_139.
Axiom proof_of_cmp_polar_values_safety_wit_140 : cmp_polar_values_safety_wit_140.
Axiom proof_of_cmp_polar_values_safety_wit_141 : cmp_polar_values_safety_wit_141.
Axiom proof_of_cmp_polar_values_safety_wit_142 : cmp_polar_values_safety_wit_142.
Axiom proof_of_cmp_polar_values_safety_wit_143 : cmp_polar_values_safety_wit_143.
Axiom proof_of_cmp_polar_values_safety_wit_144 : cmp_polar_values_safety_wit_144.
Axiom proof_of_cmp_polar_values_safety_wit_145 : cmp_polar_values_safety_wit_145.
Axiom proof_of_cmp_polar_values_safety_wit_146 : cmp_polar_values_safety_wit_146.
Axiom proof_of_cmp_polar_values_safety_wit_147 : cmp_polar_values_safety_wit_147.
Axiom proof_of_cmp_polar_values_safety_wit_148 : cmp_polar_values_safety_wit_148.
Axiom proof_of_cmp_polar_values_safety_wit_149 : cmp_polar_values_safety_wit_149.
Axiom proof_of_cmp_polar_values_safety_wit_150 : cmp_polar_values_safety_wit_150.
Axiom proof_of_cmp_polar_values_safety_wit_151 : cmp_polar_values_safety_wit_151.
Axiom proof_of_cmp_polar_values_safety_wit_152 : cmp_polar_values_safety_wit_152.
Axiom proof_of_cmp_polar_values_safety_wit_153 : cmp_polar_values_safety_wit_153.
Axiom proof_of_cmp_polar_values_safety_wit_154 : cmp_polar_values_safety_wit_154.
Axiom proof_of_cmp_polar_values_safety_wit_155 : cmp_polar_values_safety_wit_155.
Axiom proof_of_cmp_polar_values_safety_wit_156 : cmp_polar_values_safety_wit_156.
Axiom proof_of_cmp_polar_values_safety_wit_157 : cmp_polar_values_safety_wit_157.
Axiom proof_of_cmp_polar_values_safety_wit_158 : cmp_polar_values_safety_wit_158.
Axiom proof_of_cmp_polar_values_safety_wit_159 : cmp_polar_values_safety_wit_159.
Axiom proof_of_cmp_polar_values_safety_wit_160 : cmp_polar_values_safety_wit_160.
Axiom proof_of_cmp_polar_values_safety_wit_161 : cmp_polar_values_safety_wit_161.
Axiom proof_of_cmp_polar_values_safety_wit_162 : cmp_polar_values_safety_wit_162.
Axiom proof_of_cmp_polar_values_safety_wit_163 : cmp_polar_values_safety_wit_163.
Axiom proof_of_cmp_polar_values_safety_wit_164 : cmp_polar_values_safety_wit_164.
Axiom proof_of_cmp_polar_values_safety_wit_165 : cmp_polar_values_safety_wit_165.
Axiom proof_of_cmp_polar_values_safety_wit_166 : cmp_polar_values_safety_wit_166.
Axiom proof_of_cmp_polar_values_safety_wit_167 : cmp_polar_values_safety_wit_167.
Axiom proof_of_cmp_polar_values_safety_wit_168 : cmp_polar_values_safety_wit_168.
Axiom proof_of_cmp_polar_values_safety_wit_169 : cmp_polar_values_safety_wit_169.
Axiom proof_of_cmp_polar_values_return_wit_1 : cmp_polar_values_return_wit_1.
Axiom proof_of_cmp_polar_values_return_wit_2 : cmp_polar_values_return_wit_2.
Axiom proof_of_cmp_polar_values_return_wit_3 : cmp_polar_values_return_wit_3.
Axiom proof_of_cmp_polar_values_return_wit_4 : cmp_polar_values_return_wit_4.
Axiom proof_of_cmp_polar_values_return_wit_5 : cmp_polar_values_return_wit_5.
Axiom proof_of_cmp_polar_values_return_wit_6 : cmp_polar_values_return_wit_6.
Axiom proof_of_cmp_polar_values_return_wit_7 : cmp_polar_values_return_wit_7.
Axiom proof_of_cmp_polar_values_return_wit_8 : cmp_polar_values_return_wit_8.
Axiom proof_of_cmp_polar_values_return_wit_9 : cmp_polar_values_return_wit_9.
Axiom proof_of_cmp_polar_values_return_wit_10 : cmp_polar_values_return_wit_10.
Axiom proof_of_cmp_polar_values_return_wit_11 : cmp_polar_values_return_wit_11.
Axiom proof_of_cmp_polar_values_return_wit_12 : cmp_polar_values_return_wit_12.
Axiom proof_of_cmp_polar_values_return_wit_13 : cmp_polar_values_return_wit_13.
Axiom proof_of_cmp_polar_values_return_wit_14 : cmp_polar_values_return_wit_14.
Axiom proof_of_cmp_polar_values_return_wit_15 : cmp_polar_values_return_wit_15.
Axiom proof_of_cmp_polar_values_return_wit_16 : cmp_polar_values_return_wit_16.
Axiom proof_of_cmp_polar_values_return_wit_17 : cmp_polar_values_return_wit_17.
Axiom proof_of_cmp_polar_values_return_wit_18 : cmp_polar_values_return_wit_18.
Axiom proof_of_cmp_polar_values_return_wit_19 : cmp_polar_values_return_wit_19.
Axiom proof_of_cmp_polar_values_return_wit_20 : cmp_polar_values_return_wit_20.
Axiom proof_of_cmp_polar_values_return_wit_21 : cmp_polar_values_return_wit_21.
Axiom proof_of_cmp_polar_values_return_wit_22 : cmp_polar_values_return_wit_22.
Axiom proof_of_cmp_polar_values_return_wit_23 : cmp_polar_values_return_wit_23.
Axiom proof_of_cmp_polar_values_return_wit_24 : cmp_polar_values_return_wit_24.
Axiom proof_of_cmp_polar_values_return_wit_25 : cmp_polar_values_return_wit_25.
Axiom proof_of_cmp_polar_values_return_wit_26 : cmp_polar_values_return_wit_26.
Axiom proof_of_cmp_polar_values_return_wit_27 : cmp_polar_values_return_wit_27.
Axiom proof_of_cmp_polar_values_return_wit_28 : cmp_polar_values_return_wit_28.
Axiom proof_of_cmp_polar_values_return_wit_29 : cmp_polar_values_return_wit_29.
Axiom proof_of_cmp_polar_values_return_wit_30 : cmp_polar_values_return_wit_30.
Axiom proof_of_cmp_polar_values_return_wit_31 : cmp_polar_values_return_wit_31.
Axiom proof_of_cmp_polar_values_return_wit_32 : cmp_polar_values_return_wit_32.
Axiom proof_of_cmp_polar_values_return_wit_33 : cmp_polar_values_return_wit_33.
Axiom proof_of_cmp_polar_values_return_wit_34 : cmp_polar_values_return_wit_34.
Axiom proof_of_cmp_polar_values_return_wit_35 : cmp_polar_values_return_wit_35.
Axiom proof_of_cmp_polar_values_return_wit_36 : cmp_polar_values_return_wit_36.
Axiom proof_of_cmp_polar_values_return_wit_37 : cmp_polar_values_return_wit_37.
Axiom proof_of_cmp_polar_values_return_wit_38 : cmp_polar_values_return_wit_38.
Axiom proof_of_cmp_polar_values_return_wit_39 : cmp_polar_values_return_wit_39.
Axiom proof_of_cmp_polar_values_return_wit_40 : cmp_polar_values_return_wit_40.
Axiom proof_of_cmp_polar_values_return_wit_41 : cmp_polar_values_return_wit_41.
Axiom proof_of_cmp_polar_values_return_wit_42 : cmp_polar_values_return_wit_42.
Axiom proof_of_cmp_polar_values_return_wit_43 : cmp_polar_values_return_wit_43.
Axiom proof_of_cmp_polar_values_return_wit_44 : cmp_polar_values_return_wit_44.
Axiom proof_of_cmp_polar_values_return_wit_45 : cmp_polar_values_return_wit_45.
Axiom proof_of_cmp_polar_values_return_wit_46 : cmp_polar_values_return_wit_46.
Axiom proof_of_cmp_polar_values_return_wit_47 : cmp_polar_values_return_wit_47.
Axiom proof_of_cmp_polar_values_return_wit_48 : cmp_polar_values_return_wit_48.
Axiom proof_of_cmp_polar_values_return_wit_49 : cmp_polar_values_return_wit_49.
Axiom proof_of_cmp_polar_values_return_wit_50 : cmp_polar_values_return_wit_50.
Axiom proof_of_cmp_polar_values_return_wit_51 : cmp_polar_values_return_wit_51.
Axiom proof_of_cmp_polar_values_return_wit_52 : cmp_polar_values_return_wit_52.
Axiom proof_of_cmp_polar_values_return_wit_53 : cmp_polar_values_return_wit_53.
Axiom proof_of_cmp_polar_values_return_wit_54 : cmp_polar_values_return_wit_54.
Axiom proof_of_cmp_polar_values_return_wit_55 : cmp_polar_values_return_wit_55.
Axiom proof_of_cmp_polar_values_return_wit_56 : cmp_polar_values_return_wit_56.
Axiom proof_of_cmp_polar_values_return_wit_57 : cmp_polar_values_return_wit_57.
Axiom proof_of_cmp_polar_values_return_wit_58 : cmp_polar_values_return_wit_58.
Axiom proof_of_cmp_polar_values_return_wit_59 : cmp_polar_values_return_wit_59.
Axiom proof_of_cmp_polar_values_return_wit_60 : cmp_polar_values_return_wit_60.
Axiom proof_of_cmp_polar_values_return_wit_61 : cmp_polar_values_return_wit_61.
Axiom proof_of_cmp_polar_values_return_wit_62 : cmp_polar_values_return_wit_62.
Axiom proof_of_cmp_polar_values_return_wit_63 : cmp_polar_values_return_wit_63.
Axiom proof_of_cmp_polar_values_return_wit_64 : cmp_polar_values_return_wit_64.
Axiom proof_of_cmp_polar_values_return_wit_65 : cmp_polar_values_return_wit_65.
Axiom proof_of_cmp_polar_values_return_wit_66 : cmp_polar_values_return_wit_66.
Axiom proof_of_cmp_polar_values_return_wit_67 : cmp_polar_values_return_wit_67.
Axiom proof_of_cmp_polar_values_return_wit_68 : cmp_polar_values_return_wit_68.
Axiom proof_of_swap_points_safety_wit_1 : swap_points_safety_wit_1.
Axiom proof_of_swap_points_safety_wit_2 : swap_points_safety_wit_2.
Axiom proof_of_swap_points_safety_wit_3 : swap_points_safety_wit_3.
Axiom proof_of_swap_points_safety_wit_4 : swap_points_safety_wit_4.
Axiom proof_of_swap_points_safety_wit_5 : swap_points_safety_wit_5.
Axiom proof_of_swap_points_safety_wit_6 : swap_points_safety_wit_6.
Axiom proof_of_swap_points_safety_wit_7 : swap_points_safety_wit_7.
Axiom proof_of_swap_points_safety_wit_8 : swap_points_safety_wit_8.
Axiom proof_of_swap_points_safety_wit_9 : swap_points_safety_wit_9.
Axiom proof_of_swap_points_safety_wit_10 : swap_points_safety_wit_10.
Axiom proof_of_swap_points_safety_wit_11 : swap_points_safety_wit_11.
Axiom proof_of_swap_points_safety_wit_12 : swap_points_safety_wit_12.
Axiom proof_of_swap_points_safety_wit_13 : swap_points_safety_wit_13.
Axiom proof_of_swap_points_safety_wit_14 : swap_points_safety_wit_14.
Axiom proof_of_swap_points_safety_wit_15 : swap_points_safety_wit_15.
Axiom proof_of_swap_points_safety_wit_16 : swap_points_safety_wit_16.
Axiom proof_of_swap_points_safety_wit_17 : swap_points_safety_wit_17.
Axiom proof_of_swap_points_safety_wit_18 : swap_points_safety_wit_18.
Axiom proof_of_swap_points_safety_wit_19 : swap_points_safety_wit_19.
Axiom proof_of_swap_points_safety_wit_20 : swap_points_safety_wit_20.
Axiom proof_of_swap_points_safety_wit_21 : swap_points_safety_wit_21.
Axiom proof_of_swap_points_safety_wit_22 : swap_points_safety_wit_22.
Axiom proof_of_swap_points_safety_wit_23 : swap_points_safety_wit_23.
Axiom proof_of_swap_points_safety_wit_24 : swap_points_safety_wit_24.
Axiom proof_of_swap_points_return_wit_1 : swap_points_return_wit_1.
Axiom proof_of_swap_points_partial_solve_wit_1 : swap_points_partial_solve_wit_1.
Axiom proof_of_swap_points_partial_solve_wit_2 : swap_points_partial_solve_wit_2.
Axiom proof_of_swap_points_partial_solve_wit_3 : swap_points_partial_solve_wit_3.
Axiom proof_of_swap_points_partial_solve_wit_4 : swap_points_partial_solve_wit_4.
Axiom proof_of_swap_points_partial_solve_wit_5 : swap_points_partial_solve_wit_5.
Axiom proof_of_swap_points_partial_solve_wit_6 : swap_points_partial_solve_wit_6.
Axiom proof_of_swap_points_partial_solve_wit_7 : swap_points_partial_solve_wit_7.
Axiom proof_of_swap_points_partial_solve_wit_8 : swap_points_partial_solve_wit_8.
Axiom proof_of_partition_points_safety_wit_1 : partition_points_safety_wit_1.
Axiom proof_of_partition_points_safety_wit_2 : partition_points_safety_wit_2.
Axiom proof_of_partition_points_safety_wit_3 : partition_points_safety_wit_3.
Axiom proof_of_partition_points_safety_wit_4 : partition_points_safety_wit_4.
Axiom proof_of_partition_points_safety_wit_5 : partition_points_safety_wit_5.
Axiom proof_of_partition_points_safety_wit_6 : partition_points_safety_wit_6.
Axiom proof_of_partition_points_safety_wit_7 : partition_points_safety_wit_7.
Axiom proof_of_partition_points_safety_wit_8 : partition_points_safety_wit_8.
Axiom proof_of_partition_points_safety_wit_9 : partition_points_safety_wit_9.
Axiom proof_of_partition_points_safety_wit_10 : partition_points_safety_wit_10.
Axiom proof_of_partition_points_safety_wit_11 : partition_points_safety_wit_11.
Axiom proof_of_partition_points_safety_wit_12 : partition_points_safety_wit_12.
Axiom proof_of_partition_points_safety_wit_13 : partition_points_safety_wit_13.
Axiom proof_of_partition_points_safety_wit_14 : partition_points_safety_wit_14.
Axiom proof_of_partition_points_safety_wit_15 : partition_points_safety_wit_15.
Axiom proof_of_partition_points_safety_wit_16 : partition_points_safety_wit_16.
Axiom proof_of_partition_points_safety_wit_17 : partition_points_safety_wit_17.
Axiom proof_of_partition_points_safety_wit_18 : partition_points_safety_wit_18.
Axiom proof_of_partition_points_safety_wit_19 : partition_points_safety_wit_19.
Axiom proof_of_partition_points_safety_wit_20 : partition_points_safety_wit_20.
Axiom proof_of_partition_points_safety_wit_21 : partition_points_safety_wit_21.
Axiom proof_of_partition_points_safety_wit_22 : partition_points_safety_wit_22.
Axiom proof_of_partition_points_entail_wit_1 : partition_points_entail_wit_1.
Axiom proof_of_partition_points_entail_wit_2_1 : partition_points_entail_wit_2_1.
Axiom proof_of_partition_points_entail_wit_2_2 : partition_points_entail_wit_2_2.
Axiom proof_of_partition_points_return_wit_1 : partition_points_return_wit_1.
Axiom proof_of_partition_points_partial_solve_wit_1 : partition_points_partial_solve_wit_1.
Axiom proof_of_partition_points_partial_solve_wit_2 : partition_points_partial_solve_wit_2.
Axiom proof_of_partition_points_partial_solve_wit_3 : partition_points_partial_solve_wit_3.
Axiom proof_of_partition_points_partial_solve_wit_4 : partition_points_partial_solve_wit_4.
Axiom proof_of_partition_points_partial_solve_wit_5_pure : partition_points_partial_solve_wit_5_pure.
Axiom proof_of_partition_points_partial_solve_wit_5 : partition_points_partial_solve_wit_5.
Axiom proof_of_partition_points_partial_solve_wit_6_pure : partition_points_partial_solve_wit_6_pure.
Axiom proof_of_partition_points_partial_solve_wit_6 : partition_points_partial_solve_wit_6.
Axiom proof_of_partition_points_partial_solve_wit_7_pure : partition_points_partial_solve_wit_7_pure.
Axiom proof_of_partition_points_partial_solve_wit_7 : partition_points_partial_solve_wit_7.
Axiom proof_of_quicksort_points_range_safety_wit_1 : quicksort_points_range_safety_wit_1.
Axiom proof_of_quicksort_points_range_safety_wit_2 : quicksort_points_range_safety_wit_2.
Axiom proof_of_quicksort_points_range_safety_wit_3 : quicksort_points_range_safety_wit_3.
Axiom proof_of_quicksort_points_range_safety_wit_4 : quicksort_points_range_safety_wit_4.
Axiom proof_of_quicksort_points_range_safety_wit_5 : quicksort_points_range_safety_wit_5.
Axiom proof_of_quicksort_points_range_safety_wit_6 : quicksort_points_range_safety_wit_6.
Axiom proof_of_quicksort_points_range_safety_wit_7 : quicksort_points_range_safety_wit_7.
Axiom proof_of_quicksort_points_range_entail_wit_1 : quicksort_points_range_entail_wit_1.
Axiom proof_of_quicksort_points_range_return_wit_1 : quicksort_points_range_return_wit_1.
Axiom proof_of_quicksort_points_range_return_wit_2 : quicksort_points_range_return_wit_2.
Axiom proof_of_quicksort_points_range_return_wit_3 : quicksort_points_range_return_wit_3.
Axiom proof_of_quicksort_points_range_return_wit_4 : quicksort_points_range_return_wit_4.
Axiom proof_of_quicksort_points_range_partial_solve_wit_1_pure : quicksort_points_range_partial_solve_wit_1_pure.
Axiom proof_of_quicksort_points_range_partial_solve_wit_1 : quicksort_points_range_partial_solve_wit_1.
Axiom proof_of_quicksort_points_range_partial_solve_wit_2_pure : quicksort_points_range_partial_solve_wit_2_pure.
Axiom proof_of_quicksort_points_range_partial_solve_wit_2 : quicksort_points_range_partial_solve_wit_2.
Axiom proof_of_quicksort_points_range_partial_solve_wit_3_pure : quicksort_points_range_partial_solve_wit_3_pure.
Axiom proof_of_quicksort_points_range_partial_solve_wit_3 : quicksort_points_range_partial_solve_wit_3.
Axiom proof_of_quicksort_points_range_partial_solve_wit_4_pure : quicksort_points_range_partial_solve_wit_4_pure.
Axiom proof_of_quicksort_points_range_partial_solve_wit_4 : quicksort_points_range_partial_solve_wit_4.
Axiom proof_of_sort_safety_wit_1 : sort_safety_wit_1.
Axiom proof_of_sort_safety_wit_2 : sort_safety_wit_2.
Axiom proof_of_sort_safety_wit_3 : sort_safety_wit_3.
Axiom proof_of_sort_return_wit_1 : sort_return_wit_1.
Axiom proof_of_sort_partial_solve_wit_1_pure : sort_partial_solve_wit_1_pure.
Axiom proof_of_sort_partial_solve_wit_1 : sort_partial_solve_wit_1.

End VC_Correct.
