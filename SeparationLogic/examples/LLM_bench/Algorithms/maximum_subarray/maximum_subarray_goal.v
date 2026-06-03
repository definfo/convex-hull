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
Require Import SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function max -----*)

Definition max_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) ,
  “ (a_pre <= b_pre) ”
  &&  emp
|--
  “ (b_pre = (max_Z (a_pre) (b_pre))) ”
  &&  emp
.

Definition max_return_wit_2 := 
forall (b_pre: Z) (a_pre: Z) ,
  “ (a_pre > b_pre) ”
  &&  emp
|--
  “ (a_pre = (max_Z (a_pre) (b_pre))) ”
  &&  emp
.

(*----- Function max_sub_array -----*)

Definition max_sub_array_safety_wit_1 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition max_sub_array_safety_wit_2 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) ,
  “ (n_pre = 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ False ”
.

Definition max_sub_array_safety_wit_3 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) ,
  “ (n_pre <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition max_sub_array_safety_wit_4 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) ,
  “ (n_pre <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  ((( &( "res" ) )) # Int  |->_)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "cur" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition max_sub_array_safety_wit_5 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (res: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (cur = (Znth 0 l 0)) ” 
  &&  “ (res = (Znth 0 l 0)) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 10000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 10000) ” 
  &&  “ (MaxSuffixSumPrefix l 1 cur ) ” 
  &&  “ (MaxSubarraySumPrefix l 1 res ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "res" ) )) # Int  |-> res)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition max_sub_array_safety_wit_6 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (cur: Z) (res: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (INT_MIN <= (cur + (Znth i l 0) )) ” 
  &&  “ ((cur + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ (MaxSuffixSumPrefix l i cur ) ” 
  &&  “ (MaxSubarraySumPrefix l i res ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ ((cur + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cur + (Znth i l 0) )) ”
.

Definition max_sub_array_safety_wit_7 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (cur: Z) (res: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (MaxSuffixSumPrefix l (i + 1 ) cur ) ” 
  &&  “ (MaxSubarraySumPrefix l (i + 1 ) res ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "res" ) )) # Int  |-> res)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition max_sub_array_entail_wit_1 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) ,
  “ (n_pre <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000))) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Znth 0 l 0) = (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) = (Znth 0 l 0)) ” 
  &&  “ ((-10000) <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) <= 10000) ” 
  &&  “ ((-10000) <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) <= 10000) ” 
  &&  “ (MaxSuffixSumPrefix l 1 (Znth 0 l 0) ) ” 
  &&  “ (MaxSubarraySumPrefix l 1 (Znth 0 l 0) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition max_sub_array_entail_wit_2 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (res: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (cur = (Znth 0 l 0)) ” 
  &&  “ (res = (Znth 0 l 0)) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 10000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 10000) ” 
  &&  “ (MaxSuffixSumPrefix l 1 cur ) ” 
  &&  “ (MaxSubarraySumPrefix l 1 res ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000))) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (MaxSuffixSumPrefix l 1 cur ) ” 
  &&  “ (MaxSubarraySumPrefix l 1 res ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition max_sub_array_entail_wit_3 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (MaxSuffixSumPrefix l i cur ) ” 
  &&  “ (MaxSubarraySumPrefix l i res ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000))) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (INT_MIN <= (cur + (Znth i l 0) )) ” 
  &&  “ ((cur + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ (MaxSuffixSumPrefix l i cur ) ” 
  &&  “ (MaxSubarraySumPrefix l i res ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition max_sub_array_entail_wit_4 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (cur: Z) (res: Z) (retval: Z) ,
  “ (retval = (max_Z ((Znth i l 0)) ((cur + (Znth i l 0) )))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (INT_MIN <= (cur + (Znth i l 0) )) ” 
  &&  “ ((cur + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ (MaxSuffixSumPrefix l i cur ) ” 
  &&  “ (MaxSubarraySumPrefix l i res ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000))) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((-10000) <= retval) ” 
  &&  “ (retval <= 1000000000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (MaxSuffixSumPrefix l (i + 1 ) retval ) ” 
  &&  “ (MaxSubarraySumPrefix l i res ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition max_sub_array_entail_wit_5 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (cur: Z) (res: Z) (retval: Z) ,
  “ (retval = (max_Z (res) (cur))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (MaxSuffixSumPrefix l (i + 1 ) cur ) ” 
  &&  “ (MaxSubarraySumPrefix l i res ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000))) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ ((-10000) <= retval) ” 
  &&  “ (retval <= 1000000000) ” 
  &&  “ (MaxSuffixSumPrefix l (i + 1 ) cur ) ” 
  &&  “ (MaxSubarraySumPrefix l (i + 1 ) retval ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition max_sub_array_entail_wit_6 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (cur: Z) (res: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (MaxSuffixSumPrefix l (i + 1 ) cur ) ” 
  &&  “ (MaxSubarraySumPrefix l (i + 1 ) res ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000))) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (MaxSuffixSumPrefix l (i + 1 ) cur ) ” 
  &&  “ (MaxSubarraySumPrefix l (i + 1 ) res ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition max_sub_array_entail_wit_7 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (MaxSuffixSumPrefix l i cur ) ” 
  &&  “ (MaxSubarraySumPrefix l i res ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ (MaxSuffixSumPrefix l n_pre cur ) ” 
  &&  “ (MaxSubarraySumPrefix l n_pre res ) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition max_sub_array_return_wit_1 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (res: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ (MaxSuffixSumPrefix l n_pre cur ) ” 
  &&  “ (MaxSubarraySumPrefix l n_pre res ) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  “ (MaxSubarraySumPrefix l n_pre res ) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition max_sub_array_partial_solve_wit_1 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) ,
  “ (n_pre <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  “ (n_pre <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (((arr_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i arr_pre 0 0 n_pre l )
.

Definition max_sub_array_partial_solve_wit_2 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) ,
  “ (n_pre <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  “ (n_pre <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (((arr_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i arr_pre 0 0 n_pre l )
.

Definition max_sub_array_partial_solve_wit_3 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (cur: Z) (res: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (INT_MIN <= (cur + (Znth i l 0) )) ” 
  &&  “ ((cur + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ (MaxSuffixSumPrefix l i cur ) ” 
  &&  “ (MaxSubarraySumPrefix l i res ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (INT_MIN <= (cur + (Znth i l 0) )) ” 
  &&  “ ((cur + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ (MaxSuffixSumPrefix l i cur ) ” 
  &&  “ (MaxSubarraySumPrefix l i res ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (((arr_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i arr_pre i 0 n_pre l )
.

Definition max_sub_array_partial_solve_wit_4 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (cur: Z) (res: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (INT_MIN <= (cur + (Znth i l 0) )) ” 
  &&  “ ((cur + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ (MaxSuffixSumPrefix l i cur ) ” 
  &&  “ (MaxSubarraySumPrefix l i res ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (INT_MIN <= (cur + (Znth i l 0) )) ” 
  &&  “ ((cur + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ (MaxSuffixSumPrefix l i cur ) ” 
  &&  “ (MaxSubarraySumPrefix l i res ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (((arr_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i arr_pre i 0 n_pre l )
.

Definition max_sub_array_partial_solve_wit_5 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (cur: Z) (res: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (INT_MIN <= (cur + (Znth i l 0) )) ” 
  &&  “ ((cur + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ (MaxSuffixSumPrefix l i cur ) ” 
  &&  “ (MaxSubarraySumPrefix l i res ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (INT_MIN <= (cur + (Znth i l 0) )) ” 
  &&  “ ((cur + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ (MaxSuffixSumPrefix l i cur ) ” 
  &&  “ (MaxSubarraySumPrefix l i res ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition max_sub_array_partial_solve_wit_6 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (cur: Z) (res: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (MaxSuffixSumPrefix l (i + 1 ) cur ) ” 
  &&  “ (MaxSubarraySumPrefix l i res ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (MaxSuffixSumPrefix l (i + 1 ) cur ) ” 
  &&  “ (MaxSubarraySumPrefix l i res ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_max_return_wit_1 : max_return_wit_1.
Axiom proof_of_max_return_wit_2 : max_return_wit_2.
Axiom proof_of_max_sub_array_safety_wit_1 : max_sub_array_safety_wit_1.
Axiom proof_of_max_sub_array_safety_wit_2 : max_sub_array_safety_wit_2.
Axiom proof_of_max_sub_array_safety_wit_3 : max_sub_array_safety_wit_3.
Axiom proof_of_max_sub_array_safety_wit_4 : max_sub_array_safety_wit_4.
Axiom proof_of_max_sub_array_safety_wit_5 : max_sub_array_safety_wit_5.
Axiom proof_of_max_sub_array_safety_wit_6 : max_sub_array_safety_wit_6.
Axiom proof_of_max_sub_array_safety_wit_7 : max_sub_array_safety_wit_7.
Axiom proof_of_max_sub_array_entail_wit_1 : max_sub_array_entail_wit_1.
Axiom proof_of_max_sub_array_entail_wit_2 : max_sub_array_entail_wit_2.
Axiom proof_of_max_sub_array_entail_wit_3 : max_sub_array_entail_wit_3.
Axiom proof_of_max_sub_array_entail_wit_4 : max_sub_array_entail_wit_4.
Axiom proof_of_max_sub_array_entail_wit_5 : max_sub_array_entail_wit_5.
Axiom proof_of_max_sub_array_entail_wit_6 : max_sub_array_entail_wit_6.
Axiom proof_of_max_sub_array_entail_wit_7 : max_sub_array_entail_wit_7.
Axiom proof_of_max_sub_array_return_wit_1 : max_sub_array_return_wit_1.
Axiom proof_of_max_sub_array_partial_solve_wit_1 : max_sub_array_partial_solve_wit_1.
Axiom proof_of_max_sub_array_partial_solve_wit_2 : max_sub_array_partial_solve_wit_2.
Axiom proof_of_max_sub_array_partial_solve_wit_3 : max_sub_array_partial_solve_wit_3.
Axiom proof_of_max_sub_array_partial_solve_wit_4 : max_sub_array_partial_solve_wit_4.
Axiom proof_of_max_sub_array_partial_solve_wit_5 : max_sub_array_partial_solve_wit_5.
Axiom proof_of_max_sub_array_partial_solve_wit_6 : max_sub_array_partial_solve_wit_6.

End VC_Correct.
