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
Require Import SimpleC.EE.LLM_bench.Algorithms.longest_increasing_subsequence.longest_increasing_subsequence_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function lengthOfLIS -----*)

Definition lengthOfLIS_safety_wit_1 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ”
  &&  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_full dp_pre numsSize_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lengthOfLIS_safety_wit_2 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |-> 1)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_full dp_pre numsSize_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lengthOfLIS_safety_wit_3 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (ans: Z) (d: (@list Z)) (i: Z) ,
  “ (i < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (LISOuterState l d i ans ) ”
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 i d )
  **  (IntArray.undef_seg dp_pre i numsSize_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lengthOfLIS_safety_wit_4 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (i: Z) (ans: Z) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i 0 1 ) ”
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (1) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lengthOfLIS_safety_wit_5 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (ans: Z) (best: Z) (d: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth j l 0) < (Znth i l 0)) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i j best ) ”
  &&  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ (((Znth (j - 0 ) (app (d) ((cons (best) (nil)))) 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (j - 0 ) (app (d) ((cons (best) (nil)))) 0) + 1 )) ”
.

Definition lengthOfLIS_safety_wit_6 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (ans: Z) (best: Z) (d: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth j l 0) < (Znth i l 0)) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i j best ) ”
  &&  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lengthOfLIS_safety_wit_7 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (best: Z) (i: Z) (j: Z) (ans: Z) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < i) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i (j + 1 ) best ) ”
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition lengthOfLIS_safety_wit_8 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (best: Z) (i: Z) (ans: Z) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l (app (d) ((cons (best) (nil)))) (i + 1 ) ans ) ”
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition lengthOfLIS_entail_wit_1 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_full dp_pre numsSize_pre )
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ ((Zlength (d)) = 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= 0))) ” 
  &&  “ (LISOuterState l d 0 1 ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 0 d )
  **  (IntArray.undef_seg dp_pre 0 numsSize_pre )
.

Definition lengthOfLIS_entail_wit_2 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (ans: Z) (d_2: (@list Z)) (i: Z) ,
  “ (i < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ ((Zlength (d_2)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 d_2 0)) /\ ((Znth k_2 d_2 0) <= i))) ” 
  &&  “ (LISOuterState l d_2 i ans ) ”
  &&  (IntArray.seg dp_pre 0 (i + 1 ) (app (d_2) ((cons (1) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
  **  (IntArray.full nums_pre numsSize_pre l )
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i 0 1 ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (1) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_entail_wit_3 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (i: Z) (ans: Z) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((Zlength (d_2)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 d_2 0)) /\ ((Znth k_2 d_2 0) <= i))) ” 
  &&  “ (LISOuterState l d_2 i ans ) ” 
  &&  “ (LISInnerBest l d_2 i 0 1 ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d_2) ((cons (1) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  EX (best: Z)  (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i 0 best ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_entail_wit_4 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (ans: Z) (best: Z) (d: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth j l 0) < (Znth i l 0)) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 d 0)) /\ ((Znth k_2 d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i j best ) ”
  &&  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  EX (best_2: Z)  (d_2: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < i) ” 
  &&  “ ((Zlength (d_2)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d_2 0)) /\ ((Znth k d_2 0) <= i))) ” 
  &&  “ (1 <= best_2) ” 
  &&  “ (best_2 <= (i + 1 )) ” 
  &&  “ (((Znth (j - 0 ) (app (d) ((cons (best) (nil)))) 0) + 1 ) = ((Znth j d_2 0) + 1 )) ” 
  &&  “ (2 <= ((Znth (j - 0 ) (app (d) ((cons (best) (nil)))) 0) + 1 )) ” 
  &&  “ (((Znth (j - 0 ) (app (d) ((cons (best) (nil)))) 0) + 1 ) <= (i + 1 )) ” 
  &&  “ ((Znth j l 0) < (Znth i l 0)) ” 
  &&  “ (LISOuterState l d_2 i ans ) ” 
  &&  “ (LISInnerBest l d_2 i j best_2 ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d_2) ((cons (best_2) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_entail_wit_5_1 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (best_2: Z) (i: Z) (j: Z) (candidate: Z) (ans: Z) ,
  “ (candidate > (Znth (i - 0 ) (app (d_2) ((cons (best_2) (nil)))) 0)) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < i) ” 
  &&  “ ((Zlength (d_2)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 d_2 0)) /\ ((Znth k_2 d_2 0) <= i))) ” 
  &&  “ (1 <= best_2) ” 
  &&  “ (best_2 <= (i + 1 )) ” 
  &&  “ (candidate = ((Znth j d_2 0) + 1 )) ” 
  &&  “ (2 <= candidate) ” 
  &&  “ (candidate <= (i + 1 )) ” 
  &&  “ ((Znth j l 0) < (Znth i l 0)) ” 
  &&  “ (LISOuterState l d_2 i ans ) ” 
  &&  “ (LISInnerBest l d_2 i j best_2 ) ”
  &&  (IntArray.full dp_pre (i + 1 ) (replace_Znth (i) (candidate) ((app (d_2) ((cons (best_2) (nil)))))) )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  EX (best: Z)  (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < i) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i (j + 1 ) best ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_entail_wit_5_2 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (best_2: Z) (i: Z) (j: Z) (candidate: Z) (ans: Z) ,
  “ (candidate <= (Znth (i - 0 ) (app (d_2) ((cons (best_2) (nil)))) 0)) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < i) ” 
  &&  “ ((Zlength (d_2)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 d_2 0)) /\ ((Znth k_2 d_2 0) <= i))) ” 
  &&  “ (1 <= best_2) ” 
  &&  “ (best_2 <= (i + 1 )) ” 
  &&  “ (candidate = ((Znth j d_2 0) + 1 )) ” 
  &&  “ (2 <= candidate) ” 
  &&  “ (candidate <= (i + 1 )) ” 
  &&  “ ((Znth j l 0) < (Znth i l 0)) ” 
  &&  “ (LISOuterState l d_2 i ans ) ” 
  &&  “ (LISInnerBest l d_2 i j best_2 ) ”
  &&  (IntArray.seg dp_pre 0 (i + 1 ) (app (d_2) ((cons (best_2) (nil)))) )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  EX (best: Z)  (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < i) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i (j + 1 ) best ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_entail_wit_5_3 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (ans: Z) (best_2: Z) (d_2: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth j l 0) >= (Znth i l 0)) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (d_2)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 d_2 0)) /\ ((Znth k_2 d_2 0) <= i))) ” 
  &&  “ (1 <= best_2) ” 
  &&  “ (best_2 <= (i + 1 )) ” 
  &&  “ (LISOuterState l d_2 i ans ) ” 
  &&  “ (LISInnerBest l d_2 i j best_2 ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d_2) ((cons (best_2) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  EX (best: Z)  (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < i) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i (j + 1 ) best ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_entail_wit_6 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (best_2: Z) (i: Z) (j: Z) (ans: Z) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < i) ” 
  &&  “ ((Zlength (d_2)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 d_2 0)) /\ ((Znth k_2 d_2 0) <= i))) ” 
  &&  “ (1 <= best_2) ” 
  &&  “ (best_2 <= (i + 1 )) ” 
  &&  “ (LISOuterState l d_2 i ans ) ” 
  &&  “ (LISInnerBest l d_2 i (j + 1 ) best_2 ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d_2) ((cons (best_2) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  EX (best: Z)  (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i (j + 1 ) best ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_entail_wit_7 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (ans: Z) (best_2: Z) (d_2: (@list Z)) (j: Z) (i: Z) ,
  “ (j >= i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (d_2)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 d_2 0)) /\ ((Znth k_2 d_2 0) <= i))) ” 
  &&  “ (1 <= best_2) ” 
  &&  “ (best_2 <= (i + 1 )) ” 
  &&  “ (LISOuterState l d_2 i ans ) ” 
  &&  “ (LISInnerBest l d_2 i j best_2 ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d_2) ((cons (best_2) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  EX (best: Z)  (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i i best ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_entail_wit_8_1 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (best: Z) (i: Z) (ans: Z) ,
  “ ((Znth (i - 0 ) (app (d) ((cons (best) (nil)))) 0) > ans) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 d 0)) /\ ((Znth k_2 d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i i best ) ”
  &&  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  EX (best_2: Z)  (d_2: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((Zlength (d_2)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d_2 0)) /\ ((Znth k d_2 0) <= i))) ” 
  &&  “ (1 <= best_2) ” 
  &&  “ (best_2 <= (i + 1 )) ” 
  &&  “ (LISOuterState l (app (d_2) ((cons (best_2) (nil)))) (i + 1 ) (Znth (i - 0 ) (app (d) ((cons (best) (nil)))) 0) ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d_2) ((cons (best_2) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_entail_wit_8_2 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (best_2: Z) (i: Z) (ans: Z) ,
  “ ((Znth (i - 0 ) (app (d_2) ((cons (best_2) (nil)))) 0) <= ans) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((Zlength (d_2)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 d_2 0)) /\ ((Znth k_2 d_2 0) <= i))) ” 
  &&  “ (1 <= best_2) ” 
  &&  “ (best_2 <= (i + 1 )) ” 
  &&  “ (LISOuterState l d_2 i ans ) ” 
  &&  “ (LISInnerBest l d_2 i i best_2 ) ”
  &&  (IntArray.seg dp_pre 0 (i + 1 ) (app (d_2) ((cons (best_2) (nil)))) )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  EX (best: Z)  (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l (app (d) ((cons (best) (nil)))) (i + 1 ) ans ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_entail_wit_9 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (best: Z) (i: Z) (ans: Z) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((Zlength (d_2)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 d_2 0)) /\ ((Znth k_2 d_2 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l (app (d_2) ((cons (best) (nil)))) (i + 1 ) ans ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d_2) ((cons (best) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numsSize_pre) ” 
  &&  “ ((Zlength (d)) = (i + 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= (i + 1 )))) ” 
  &&  “ (LISOuterState l d (i + 1 ) ans ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_return_wit_1 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (ans: Z) (d_2: (@list Z)) (i: Z) ,
  “ (i >= numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ ((Zlength (d_2)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d_2 0)) /\ ((Znth k d_2 0) <= i))) ” 
  &&  “ (LISOuterState l d_2 i ans ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 i d_2 )
  **  (IntArray.undef_seg dp_pre i numsSize_pre )
|--
  EX (d: (@list Z)) ,
  “ (LISLength l ans ) ” 
  &&  “ (LISDPState l d numsSize_pre ) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= numsSize_pre) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full dp_pre numsSize_pre d )
.

Definition lengthOfLIS_partial_solve_wit_1 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (ans: Z) (d: (@list Z)) (i: Z) ,
  “ (i < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (LISOuterState l d i ans ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 i d )
  **  (IntArray.undef_seg dp_pre i numsSize_pre )
|--
  “ (i < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (LISOuterState l d i ans ) ”
  &&  (((dp_pre + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 i d )
.

Definition lengthOfLIS_partial_solve_wit_2 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (ans: Z) (best: Z) (d: (@list Z)) (j: Z) (i: Z) ,
  “ (j < i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i j best ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ (j < i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i j best ) ”
  &&  (((nums_pre + (j * sizeof(INT) ) )) # Int  |-> (Znth j l 0))
  **  (IntArray.missing_i nums_pre j 0 numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_partial_solve_wit_3 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (ans: Z) (best: Z) (d: (@list Z)) (j: Z) (i: Z) ,
  “ (j < i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i j best ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ (j < i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i j best ) ”
  &&  (((nums_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i nums_pre i 0 numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_partial_solve_wit_4 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (ans: Z) (best: Z) (d: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth j l 0) < (Znth i l 0)) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i j best ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ ((Znth j l 0) < (Znth i l 0)) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i j best ) ”
  &&  (((dp_pre + (j * sizeof(INT) ) )) # Int  |-> (Znth (j - 0 ) (app (d) ((cons (best) (nil)))) 0))
  **  (IntArray.missing_i dp_pre j 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_partial_solve_wit_5 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (best: Z) (i: Z) (j: Z) (candidate: Z) (ans: Z) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < i) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (candidate = ((Znth j d 0) + 1 )) ” 
  &&  “ (2 <= candidate) ” 
  &&  “ (candidate <= (i + 1 )) ” 
  &&  “ ((Znth j l 0) < (Znth i l 0)) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i j best ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < i) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (candidate = ((Znth j d 0) + 1 )) ” 
  &&  “ (2 <= candidate) ” 
  &&  “ (candidate <= (i + 1 )) ” 
  &&  “ ((Znth j l 0) < (Znth i l 0)) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i j best ) ”
  &&  (((dp_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth (i - 0 ) (app (d) ((cons (best) (nil)))) 0))
  **  (IntArray.missing_i dp_pre i 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_partial_solve_wit_6 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (best: Z) (i: Z) (j: Z) (candidate: Z) (ans: Z) ,
  “ (candidate > (Znth (i - 0 ) (app (d) ((cons (best) (nil)))) 0)) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < i) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (candidate = ((Znth j d 0) + 1 )) ” 
  &&  “ (2 <= candidate) ” 
  &&  “ (candidate <= (i + 1 )) ” 
  &&  “ ((Znth j l 0) < (Znth i l 0)) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i j best ) ”
  &&  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ (candidate > (Znth (i - 0 ) (app (d) ((cons (best) (nil)))) 0)) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < i) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (candidate = ((Znth j d 0) + 1 )) ” 
  &&  “ (2 <= candidate) ” 
  &&  “ (candidate <= (i + 1 )) ” 
  &&  “ ((Znth j l 0) < (Znth i l 0)) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i j best ) ”
  &&  (((dp_pre + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i dp_pre i 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_partial_solve_wit_7 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (best: Z) (i: Z) (ans: Z) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i i best ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i i best ) ”
  &&  (((dp_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth (i - 0 ) (app (d) ((cons (best) (nil)))) 0))
  **  (IntArray.missing_i dp_pre i 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_partial_solve_wit_8 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (best: Z) (i: Z) (ans: Z) ,
  “ ((Znth (i - 0 ) (app (d) ((cons (best) (nil)))) 0) > ans) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i i best ) ”
  &&  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ ((Znth (i - 0 ) (app (d) ((cons (best) (nil)))) 0) > ans) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((Zlength (d)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((1 <= (Znth k d 0)) /\ ((Znth k d 0) <= i))) ” 
  &&  “ (1 <= best) ” 
  &&  “ (best <= (i + 1 )) ” 
  &&  “ (LISOuterState l d i ans ) ” 
  &&  “ (LISInnerBest l d i i best ) ”
  &&  (((dp_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth (i - 0 ) (app (d) ((cons (best) (nil)))) 0))
  **  (IntArray.missing_i dp_pre i 0 (i + 1 ) (app (d) ((cons (best) (nil)))) )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_lengthOfLIS_safety_wit_1 : lengthOfLIS_safety_wit_1.
Axiom proof_of_lengthOfLIS_safety_wit_2 : lengthOfLIS_safety_wit_2.
Axiom proof_of_lengthOfLIS_safety_wit_3 : lengthOfLIS_safety_wit_3.
Axiom proof_of_lengthOfLIS_safety_wit_4 : lengthOfLIS_safety_wit_4.
Axiom proof_of_lengthOfLIS_safety_wit_5 : lengthOfLIS_safety_wit_5.
Axiom proof_of_lengthOfLIS_safety_wit_6 : lengthOfLIS_safety_wit_6.
Axiom proof_of_lengthOfLIS_safety_wit_7 : lengthOfLIS_safety_wit_7.
Axiom proof_of_lengthOfLIS_safety_wit_8 : lengthOfLIS_safety_wit_8.
Axiom proof_of_lengthOfLIS_entail_wit_1 : lengthOfLIS_entail_wit_1.
Axiom proof_of_lengthOfLIS_entail_wit_2 : lengthOfLIS_entail_wit_2.
Axiom proof_of_lengthOfLIS_entail_wit_3 : lengthOfLIS_entail_wit_3.
Axiom proof_of_lengthOfLIS_entail_wit_4 : lengthOfLIS_entail_wit_4.
Axiom proof_of_lengthOfLIS_entail_wit_5_1 : lengthOfLIS_entail_wit_5_1.
Axiom proof_of_lengthOfLIS_entail_wit_5_2 : lengthOfLIS_entail_wit_5_2.
Axiom proof_of_lengthOfLIS_entail_wit_5_3 : lengthOfLIS_entail_wit_5_3.
Axiom proof_of_lengthOfLIS_entail_wit_6 : lengthOfLIS_entail_wit_6.
Axiom proof_of_lengthOfLIS_entail_wit_7 : lengthOfLIS_entail_wit_7.
Axiom proof_of_lengthOfLIS_entail_wit_8_1 : lengthOfLIS_entail_wit_8_1.
Axiom proof_of_lengthOfLIS_entail_wit_8_2 : lengthOfLIS_entail_wit_8_2.
Axiom proof_of_lengthOfLIS_entail_wit_9 : lengthOfLIS_entail_wit_9.
Axiom proof_of_lengthOfLIS_return_wit_1 : lengthOfLIS_return_wit_1.
Axiom proof_of_lengthOfLIS_partial_solve_wit_1 : lengthOfLIS_partial_solve_wit_1.
Axiom proof_of_lengthOfLIS_partial_solve_wit_2 : lengthOfLIS_partial_solve_wit_2.
Axiom proof_of_lengthOfLIS_partial_solve_wit_3 : lengthOfLIS_partial_solve_wit_3.
Axiom proof_of_lengthOfLIS_partial_solve_wit_4 : lengthOfLIS_partial_solve_wit_4.
Axiom proof_of_lengthOfLIS_partial_solve_wit_5 : lengthOfLIS_partial_solve_wit_5.
Axiom proof_of_lengthOfLIS_partial_solve_wit_6 : lengthOfLIS_partial_solve_wit_6.
Axiom proof_of_lengthOfLIS_partial_solve_wit_7 : lengthOfLIS_partial_solve_wit_7.
Axiom proof_of_lengthOfLIS_partial_solve_wit_8 : lengthOfLIS_partial_solve_wit_8.

End VC_Correct.
