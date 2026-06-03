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
Require Import SimpleC.EE.LLM_bench.Algorithms.split_array_largest_sum.split_array_largest_sum_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function check -----*)

Definition check_safety_wit_1 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ”
  &&  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition check_safety_wit_2 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ”
  &&  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |-> 1)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_safety_wit_3 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "cnt" ) )) # Int  |-> 1)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_safety_wit_4 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) ,
  “ ((Znth i l 0) > cap_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt <= (i + 1 )) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= cap_pre) ” 
  &&  “ (PrefixSplitState l cap_pre i cnt cur ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  ((( &( "x" ) )) # Int  |-> (Znth i l 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_safety_wit_5 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) ,
  “ ((Znth i l 0) <= cap_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt <= (i + 1 )) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= cap_pre) ” 
  &&  “ (PrefixSplitState l cap_pre i cnt cur ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  ((( &( "x" ) )) # Int  |-> (Znth i l 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ ((cur + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cur + (Znth i l 0) )) ”
.

Definition check_safety_wit_6 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) ,
  “ ((cur + (Znth i l 0) ) > cap_pre) ” 
  &&  “ ((Znth i l 0) <= cap_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt <= (i + 1 )) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= cap_pre) ” 
  &&  “ (PrefixSplitState l cap_pre i cnt cur ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  ((( &( "x" ) )) # Int  |-> (Znth i l 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ ((cnt + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cnt + 1 )) ”
.

Definition check_safety_wit_7 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) ,
  “ ((cur + (Znth i l 0) ) > cap_pre) ” 
  &&  “ ((Znth i l 0) <= cap_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt <= (i + 1 )) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= cap_pre) ” 
  &&  “ (PrefixSplitState l cap_pre i cnt cur ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  ((( &( "x" ) )) # Int  |-> (Znth i l 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition check_safety_wit_8 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) ,
  “ ((cur + (Znth i l 0) ) <= cap_pre) ” 
  &&  “ ((Znth i l 0) <= cap_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt <= (i + 1 )) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= cap_pre) ” 
  &&  “ (PrefixSplitState l cap_pre i cnt cur ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  ((( &( "x" ) )) # Int  |-> (Znth i l 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ ((cur + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cur + (Znth i l 0) )) ”
.

Definition check_safety_wit_9 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) ,
  “ ((cur + (Znth i l 0) ) <= cap_pre) ” 
  &&  “ ((Znth i l 0) <= cap_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt <= (i + 1 )) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= cap_pre) ” 
  &&  “ (PrefixSplitState l cap_pre i cnt cur ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "cur" ) )) # Int  |-> (cur + (Znth i l 0) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition check_safety_wit_10 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) ,
  “ ((cur + (Znth i l 0) ) > cap_pre) ” 
  &&  “ ((Znth i l 0) <= cap_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt <= (i + 1 )) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= cap_pre) ” 
  &&  “ (PrefixSplitState l cap_pre i cnt cur ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> (cnt + 1 ))
  **  ((( &( "cur" ) )) # Int  |-> (Znth i l 0))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition check_safety_wit_11 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) ,
  “ (cnt <= m_pre) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt <= (i + 1 )) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= cap_pre) ” 
  &&  “ (PrefixSplitState l cap_pre i cnt cur ) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition check_safety_wit_12 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) ,
  “ (cnt > m_pre) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt <= (i + 1 )) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= cap_pre) ” 
  &&  “ (PrefixSplitState l cap_pre i cnt cur ) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_entail_wit_1 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (0 + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (PrefixSplitState l cap_pre 0 1 0 ) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition check_entail_wit_2_1 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) ,
  “ ((cur + (Znth i l 0) ) > cap_pre) ” 
  &&  “ ((Znth i l 0) <= cap_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt <= (i + 1 )) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= cap_pre) ” 
  &&  “ (PrefixSplitState l cap_pre i cnt cur ) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (1 <= (cnt + 1 )) ” 
  &&  “ ((cnt + 1 ) <= ((i + 1 ) + 1 )) ” 
  &&  “ (0 <= (Znth i l 0)) ” 
  &&  “ ((Znth i l 0) <= cap_pre) ” 
  &&  “ (PrefixSplitState l cap_pre (i + 1 ) (cnt + 1 ) (Znth i l 0) ) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition check_entail_wit_2_2 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) ,
  “ ((cur + (Znth i l 0) ) <= cap_pre) ” 
  &&  “ ((Znth i l 0) <= cap_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt <= (i + 1 )) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= cap_pre) ” 
  &&  “ (PrefixSplitState l cap_pre i cnt cur ) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt <= ((i + 1 ) + 1 )) ” 
  &&  “ (0 <= (cur + (Znth i l 0) )) ” 
  &&  “ ((cur + (Znth i l 0) ) <= cap_pre) ” 
  &&  “ (PrefixSplitState l cap_pre (i + 1 ) cnt (cur + (Znth i l 0) ) ) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition check_return_wit_1 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) ,
  “ (cnt > m_pre) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt <= (i + 1 )) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= cap_pre) ” 
  &&  “ (PrefixSplitState l cap_pre i cnt cur ) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((0 = 1) -> (CanSplit l m_pre cap_pre )) ” 
  &&  “ ((0 = 0) -> (CannotSplit l m_pre cap_pre )) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition check_return_wit_2 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) ,
  “ (cnt <= m_pre) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt <= (i + 1 )) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= cap_pre) ” 
  &&  “ (PrefixSplitState l cap_pre i cnt cur ) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ ((1 = 1) -> (CanSplit l m_pre cap_pre )) ” 
  &&  “ ((1 = 0) -> (CannotSplit l m_pre cap_pre )) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition check_return_wit_3 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) ,
  “ ((Znth i l 0) > cap_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt <= (i + 1 )) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= cap_pre) ” 
  &&  “ (PrefixSplitState l cap_pre i cnt cur ) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((0 = 1) -> (CanSplit l m_pre cap_pre )) ” 
  &&  “ ((0 = 0) -> (CannotSplit l m_pre cap_pre )) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition check_partial_solve_wit_1 := 
forall (cap_pre: Z) (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (cnt: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt <= (i + 1 )) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= cap_pre) ” 
  &&  “ (PrefixSplitState l cap_pre i cnt cur ) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (0 <= cap_pre) ” 
  &&  “ (cap_pre <= 1000000000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) < 100000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt <= (i + 1 )) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= cap_pre) ” 
  &&  “ (PrefixSplitState l cap_pre i cnt cur ) ”
  &&  (((arr_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i arr_pre i 0 n_pre l )
.

(*----- Function splitArrayLargestSum -----*)

Definition splitArrayLargestSum_safety_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre ans ) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 1000000000) ”
  &&  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition splitArrayLargestSum_safety_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre ans ) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 1000000000) ”
  &&  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition splitArrayLargestSum_safety_wit_3 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) ,
  “ (left < right) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ” 
  &&  “ (0 <= left) ” 
  &&  “ (right <= 1000000000) ” 
  &&  “ (left <= right) ” 
  &&  “ (left <= res) ” 
  &&  “ (res <= right) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre res ) ”
  &&  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ ((left + ((right - left ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + ((right - left ) ÷ 2 ) )) ”
.

Definition splitArrayLargestSum_safety_wit_4 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) ,
  “ (left < right) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ” 
  &&  “ (0 <= left) ” 
  &&  “ (right <= 1000000000) ” 
  &&  “ (left <= right) ” 
  &&  “ (left <= res) ” 
  &&  “ (res <= right) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre res ) ”
  &&  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ (((right - left ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition splitArrayLargestSum_safety_wit_5 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) ,
  “ (left < right) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ” 
  &&  “ (0 <= left) ” 
  &&  “ (right <= 1000000000) ” 
  &&  “ (left <= right) ” 
  &&  “ (left <= res) ” 
  &&  “ (res <= right) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre res ) ”
  &&  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ ((right - left ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (right - left )) ”
.

Definition splitArrayLargestSum_safety_wit_6 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) ,
  “ (left < right) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ” 
  &&  “ (0 <= left) ” 
  &&  “ (right <= 1000000000) ” 
  &&  “ (left <= right) ” 
  &&  “ (left <= res) ” 
  &&  “ (res <= right) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre res ) ”
  &&  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition splitArrayLargestSum_safety_wit_7 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((retval = 1) -> (CanSplit l m_pre (left + ((right - left ) ÷ 2 ) ) )) ” 
  &&  “ ((retval = 0) -> (CannotSplit l m_pre (left + ((right - left ) ÷ 2 ) ) )) ” 
  &&  “ (left < right) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ” 
  &&  “ (0 <= left) ” 
  &&  “ (right <= 1000000000) ” 
  &&  “ (left <= right) ” 
  &&  “ (left <= res) ” 
  &&  “ (res <= right) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre res ) ” 
  &&  “ (retval = 0) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> (left + ((right - left ) ÷ 2 ) ))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ (((left + ((right - left ) ÷ 2 ) ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((left + ((right - left ) ÷ 2 ) ) + 1 )) ”
.

Definition splitArrayLargestSum_safety_wit_8 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((retval = 1) -> (CanSplit l m_pre (left + ((right - left ) ÷ 2 ) ) )) ” 
  &&  “ ((retval = 0) -> (CannotSplit l m_pre (left + ((right - left ) ÷ 2 ) ) )) ” 
  &&  “ (left < right) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ” 
  &&  “ (0 <= left) ” 
  &&  “ (right <= 1000000000) ” 
  &&  “ (left <= right) ” 
  &&  “ (left <= res) ” 
  &&  “ (res <= right) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre res ) ” 
  &&  “ (retval = 0) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> (left + ((right - left ) ÷ 2 ) ))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition splitArrayLargestSum_entail_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100000000))) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre ans ) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 1000000000) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  EX (res: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (1000000000 <= 1000000000) ” 
  &&  “ (0 <= 1000000000) ” 
  &&  “ (0 <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre res ) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition splitArrayLargestSum_entail_wit_2_1 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res_2: Z) (right: Z) (left: Z) (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((retval = 1) -> (CanSplit l m_pre (left + ((right - left ) ÷ 2 ) ) )) ” 
  &&  “ ((retval = 0) -> (CannotSplit l m_pre (left + ((right - left ) ÷ 2 ) ) )) ” 
  &&  “ (left < right) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ” 
  &&  “ (0 <= left) ” 
  &&  “ (right <= 1000000000) ” 
  &&  “ (left <= right) ” 
  &&  “ (left <= res_2) ” 
  &&  “ (res_2 <= right) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre res_2 ) ” 
  &&  “ (retval = 0) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  EX (res: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ” 
  &&  “ (0 <= ((left + ((right - left ) ÷ 2 ) ) + 1 )) ” 
  &&  “ (right <= 1000000000) ” 
  &&  “ (((left + ((right - left ) ÷ 2 ) ) + 1 ) <= right) ” 
  &&  “ (((left + ((right - left ) ÷ 2 ) ) + 1 ) <= res) ” 
  &&  “ (res <= right) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre res ) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition splitArrayLargestSum_entail_wit_2_2 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res_2: Z) (right: Z) (left: Z) (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((retval = 1) -> (CanSplit l m_pre (left + ((right - left ) ÷ 2 ) ) )) ” 
  &&  “ ((retval = 0) -> (CannotSplit l m_pre (left + ((right - left ) ÷ 2 ) ) )) ” 
  &&  “ (left < right) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ” 
  &&  “ (0 <= left) ” 
  &&  “ (right <= 1000000000) ” 
  &&  “ (left <= right) ” 
  &&  “ (left <= res_2) ” 
  &&  “ (res_2 <= right) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre res_2 ) ” 
  &&  “ (retval <> 0) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  EX (res: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + ((right - left ) ÷ 2 ) ) <= 1000000000) ” 
  &&  “ (left <= (left + ((right - left ) ÷ 2 ) )) ” 
  &&  “ (left <= res) ” 
  &&  “ (res <= (left + ((right - left ) ÷ 2 ) )) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre res ) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition splitArrayLargestSum_return_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) ,
  “ (left >= right) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ” 
  &&  “ (0 <= left) ” 
  &&  “ (right <= 1000000000) ” 
  &&  “ (left <= right) ” 
  &&  “ (left <= res) ” 
  &&  “ (res <= right) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre res ) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  “ (MinimizedMaxSegmentSum l m_pre left ) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition splitArrayLargestSum_partial_solve_wit_1_pure := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) ,
  “ (left < right) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100000000))) ” 
  &&  “ (0 <= left) ” 
  &&  “ (right <= 1000000000) ” 
  &&  “ (left <= right) ” 
  &&  “ (left <= res) ” 
  &&  “ (res <= right) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre res ) ”
  &&  ((( &( "ok" ) )) # Int  |->_)
  **  ((( &( "mid" ) )) # Int  |-> (left + ((right - left ) ÷ 2 ) ))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ” 
  &&  “ ((left + ((right - left ) ÷ 2 ) ) <= 1000000000) ” 
  &&  “ (0 <= (left + ((right - left ) ÷ 2 ) )) ”
.

Definition splitArrayLargestSum_partial_solve_wit_1_aux := 
forall (m_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (right: Z) (left: Z) ,
  “ (left < right) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100000000))) ” 
  &&  “ (0 <= left) ” 
  &&  “ (right <= 1000000000) ” 
  &&  “ (left <= right) ” 
  &&  “ (left <= res) ” 
  &&  “ (res <= right) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre res ) ”
  &&  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100000000))) ” 
  &&  “ ((left + ((right - left ) ÷ 2 ) ) <= 1000000000) ” 
  &&  “ (0 <= (left + ((right - left ) ÷ 2 ) )) ” 
  &&  “ (left < right) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100000000))) ” 
  &&  “ (0 <= left) ” 
  &&  “ (right <= 1000000000) ” 
  &&  “ (left <= right) ” 
  &&  “ (left <= res) ” 
  &&  “ (res <= right) ” 
  &&  “ (MinimizedMaxSegmentSum l m_pre res ) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition splitArrayLargestSum_partial_solve_wit_1 := splitArrayLargestSum_partial_solve_wit_1_pure -> splitArrayLargestSum_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_check_safety_wit_1 : check_safety_wit_1.
Axiom proof_of_check_safety_wit_2 : check_safety_wit_2.
Axiom proof_of_check_safety_wit_3 : check_safety_wit_3.
Axiom proof_of_check_safety_wit_4 : check_safety_wit_4.
Axiom proof_of_check_safety_wit_5 : check_safety_wit_5.
Axiom proof_of_check_safety_wit_6 : check_safety_wit_6.
Axiom proof_of_check_safety_wit_7 : check_safety_wit_7.
Axiom proof_of_check_safety_wit_8 : check_safety_wit_8.
Axiom proof_of_check_safety_wit_9 : check_safety_wit_9.
Axiom proof_of_check_safety_wit_10 : check_safety_wit_10.
Axiom proof_of_check_safety_wit_11 : check_safety_wit_11.
Axiom proof_of_check_safety_wit_12 : check_safety_wit_12.
Axiom proof_of_check_entail_wit_1 : check_entail_wit_1.
Axiom proof_of_check_entail_wit_2_1 : check_entail_wit_2_1.
Axiom proof_of_check_entail_wit_2_2 : check_entail_wit_2_2.
Axiom proof_of_check_return_wit_1 : check_return_wit_1.
Axiom proof_of_check_return_wit_2 : check_return_wit_2.
Axiom proof_of_check_return_wit_3 : check_return_wit_3.
Axiom proof_of_check_partial_solve_wit_1 : check_partial_solve_wit_1.
Axiom proof_of_splitArrayLargestSum_safety_wit_1 : splitArrayLargestSum_safety_wit_1.
Axiom proof_of_splitArrayLargestSum_safety_wit_2 : splitArrayLargestSum_safety_wit_2.
Axiom proof_of_splitArrayLargestSum_safety_wit_3 : splitArrayLargestSum_safety_wit_3.
Axiom proof_of_splitArrayLargestSum_safety_wit_4 : splitArrayLargestSum_safety_wit_4.
Axiom proof_of_splitArrayLargestSum_safety_wit_5 : splitArrayLargestSum_safety_wit_5.
Axiom proof_of_splitArrayLargestSum_safety_wit_6 : splitArrayLargestSum_safety_wit_6.
Axiom proof_of_splitArrayLargestSum_safety_wit_7 : splitArrayLargestSum_safety_wit_7.
Axiom proof_of_splitArrayLargestSum_safety_wit_8 : splitArrayLargestSum_safety_wit_8.
Axiom proof_of_splitArrayLargestSum_entail_wit_1 : splitArrayLargestSum_entail_wit_1.
Axiom proof_of_splitArrayLargestSum_entail_wit_2_1 : splitArrayLargestSum_entail_wit_2_1.
Axiom proof_of_splitArrayLargestSum_entail_wit_2_2 : splitArrayLargestSum_entail_wit_2_2.
Axiom proof_of_splitArrayLargestSum_return_wit_1 : splitArrayLargestSum_return_wit_1.
Axiom proof_of_splitArrayLargestSum_partial_solve_wit_1_pure : splitArrayLargestSum_partial_solve_wit_1_pure.
Axiom proof_of_splitArrayLargestSum_partial_solve_wit_1 : splitArrayLargestSum_partial_solve_wit_1.

End VC_Correct.
