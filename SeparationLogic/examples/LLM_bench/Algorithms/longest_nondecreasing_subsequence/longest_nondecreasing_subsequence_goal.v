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
Require Import SimpleC.EE.LLM_bench.Algorithms.longest_nondecreasing_subsequence.longest_nondecreasing_subsequence_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function lengthOfLNDS -----*)

Definition lengthOfLNDS_safety_wit_1 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (tails_l: (@list Z)) (l: (@list Z)) ,
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_l)) = numsSize_pre) ”
  &&  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "tails" ) )) # Ptr  |-> tails_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lengthOfLNDS_safety_wit_2 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (tails_l: (@list Z)) (l: (@list Z)) ,
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_l)) = numsSize_pre) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "tails" ) )) # Ptr  |-> tails_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lengthOfLNDS_safety_wit_3 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (tails_cur: (@list Z)) (i: Z) (len: Z) (x: Z) ,
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur)) len ) ”
  &&  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "tails" ) )) # Ptr  |-> tails_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lengthOfLNDS_safety_wit_4 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (right: Z) (left: Z) (x: Z) (len: Z) (i: Z) (tails_cur: (@list Z)) ,
  “ (left < right) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= right) ” 
  &&  “ (right <= len) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_cur)) len x left right ) ”
  &&  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "tails" ) )) # Ptr  |-> tails_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur )
|--
  “ ((left + ((right - left ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + ((right - left ) ÷ 2 ) )) ”
.

Definition lengthOfLNDS_safety_wit_5 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (right: Z) (left: Z) (x: Z) (len: Z) (i: Z) (tails_cur: (@list Z)) ,
  “ (left < right) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= right) ” 
  &&  “ (right <= len) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_cur)) len x left right ) ”
  &&  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "tails" ) )) # Ptr  |-> tails_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur )
|--
  “ (((right - left ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition lengthOfLNDS_safety_wit_6 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (right: Z) (left: Z) (x: Z) (len: Z) (i: Z) (tails_cur: (@list Z)) ,
  “ (left < right) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= right) ” 
  &&  “ (right <= len) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_cur)) len x left right ) ”
  &&  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "tails" ) )) # Ptr  |-> tails_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur )
|--
  “ ((right - left ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (right - left )) ”
.

Definition lengthOfLNDS_safety_wit_7 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (right: Z) (left: Z) (x: Z) (len: Z) (i: Z) (tails_cur: (@list Z)) ,
  “ (left < right) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= right) ” 
  &&  “ (right <= len) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_cur)) len x left right ) ”
  &&  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "tails" ) )) # Ptr  |-> tails_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition lengthOfLNDS_safety_wit_8 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (tails_cur: (@list Z)) (i: Z) (len: Z) (x: Z) (left: Z) (right: Z) (mid: Z) ,
  “ ((Znth mid tails_cur 0) <= x) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < right) ” 
  &&  “ (right <= len) ” 
  &&  “ (left <= mid) ” 
  &&  “ (mid < right) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_cur)) len x left right ) ”
  &&  (IntArray.full tails_pre numsSize_pre tails_cur )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "tails" ) )) # Ptr  |-> tails_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  (IntArray.full nums_pre numsSize_pre l )
|--
  “ ((mid + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (mid + 1 )) ”
.

Definition lengthOfLNDS_safety_wit_9 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (tails_cur: (@list Z)) (i: Z) (len: Z) (x: Z) (left: Z) (right: Z) (mid: Z) ,
  “ ((Znth mid tails_cur 0) <= x) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < right) ” 
  &&  “ (right <= len) ” 
  &&  “ (left <= mid) ” 
  &&  “ (mid < right) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_cur)) len x left right ) ”
  &&  (IntArray.full tails_pre numsSize_pre tails_cur )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "tails" ) )) # Ptr  |-> tails_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  (IntArray.full nums_pre numsSize_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lengthOfLNDS_safety_wit_10 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (tails_old: (@list Z)) (i: Z) (len: Z) (x: Z) (left: Z) (right: Z) ,
  “ (left = len) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_old)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= len) ” 
  &&  “ (right = left) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_old)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_old)) len x left left ) ”
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "tails" ) )) # Ptr  |-> tails_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre (app ((sublist (0) (left) (tails_old))) ((cons (x) ((sublist ((left + 1 )) (numsSize_pre) (tails_old)))))) )
|--
  “ ((len + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (len + 1 )) ”
.

Definition lengthOfLNDS_safety_wit_11 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (tails_old: (@list Z)) (i: Z) (len: Z) (x: Z) (left: Z) (right: Z) ,
  “ (left = len) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_old)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= len) ” 
  &&  “ (right = left) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_old)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_old)) len x left left ) ”
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "tails" ) )) # Ptr  |-> tails_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre (app ((sublist (0) (left) (tails_old))) ((cons (x) ((sublist ((left + 1 )) (numsSize_pre) (tails_old)))))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lengthOfLNDS_safety_wit_12 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (tails_cur: (@list Z)) (i: Z) (len: Z) (x: Z) (left: Z) (right: Z) ,
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= (i + 1 )) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= len) ” 
  &&  “ (right = left) ” 
  &&  “ (LNDTailsState l (i + 1 ) (sublist (0) (len) (tails_cur)) len ) ”
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "tails" ) )) # Ptr  |-> tails_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition lengthOfLNDS_entail_wit_1 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (tails_l: (@list Z)) (l: (@list Z)) ,
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_l)) = numsSize_pre) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_l )
|--
  EX (tails_cur: (@list Z)) ,
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (LNDTailsState l 0 (sublist (0) (0) (tails_cur)) 0 ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur )
.

Definition lengthOfLNDS_entail_wit_2 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (len: Z) (i: Z) (tails_cur_2: (@list Z)) ,
  “ (i < numsSize_pre) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur_2)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur_2)) len ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur_2 )
|--
  EX (tails_cur: (@list Z)) ,
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ ((Znth i l 0) = (Znth i l 0)) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur)) len ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur )
.

Definition lengthOfLNDS_entail_wit_3 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (tails_cur_2: (@list Z)) (i: Z) (len: Z) (x: Z) ,
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur_2)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur_2)) len ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur_2 )
|--
  EX (tails_cur: (@list Z)) ,
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= len) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_cur)) len x 0 len ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur )
.

Definition lengthOfLNDS_entail_wit_4 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (right: Z) (left: Z) (x: Z) (len: Z) (i: Z) (tails_cur_2: (@list Z)) ,
  “ (left < right) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur_2)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= right) ” 
  &&  “ (right <= len) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur_2)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_cur_2)) len x left right ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur_2 )
|--
  EX (tails_cur: (@list Z)) ,
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < right) ” 
  &&  “ (right <= len) ” 
  &&  “ (left <= (left + ((right - left ) ÷ 2 ) )) ” 
  &&  “ ((left + ((right - left ) ÷ 2 ) ) < right) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_cur)) len x left right ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur )
.

Definition lengthOfLNDS_entail_wit_5_1 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (tails_cur_2: (@list Z)) (i: Z) (len: Z) (x: Z) (left: Z) (right: Z) (mid: Z) ,
  “ ((Znth mid tails_cur_2 0) > x) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur_2)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < right) ” 
  &&  “ (right <= len) ” 
  &&  “ (left <= mid) ” 
  &&  “ (mid < right) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur_2)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_cur_2)) len x left right ) ”
  &&  (IntArray.full tails_pre numsSize_pre tails_cur_2 )
  **  (IntArray.full nums_pre numsSize_pre l )
|--
  EX (tails_cur: (@list Z)) ,
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= mid) ” 
  &&  “ (mid <= len) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_cur)) len x left mid ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur )
.

Definition lengthOfLNDS_entail_wit_5_2 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (tails_cur_2: (@list Z)) (i: Z) (len: Z) (x: Z) (left: Z) (right: Z) (mid: Z) ,
  “ ((Znth mid tails_cur_2 0) <= x) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur_2)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < right) ” 
  &&  “ (right <= len) ” 
  &&  “ (left <= mid) ” 
  &&  “ (mid < right) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur_2)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_cur_2)) len x left right ) ”
  &&  (IntArray.full tails_pre numsSize_pre tails_cur_2 )
  **  (IntArray.full nums_pre numsSize_pre l )
|--
  EX (tails_cur: (@list Z)) ,
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= (mid + 1 )) ” 
  &&  “ ((mid + 1 ) <= right) ” 
  &&  “ (right <= len) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_cur)) len x (mid + 1 ) right ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur )
.

Definition lengthOfLNDS_entail_wit_6 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (right: Z) (left: Z) (x: Z) (len: Z) (i: Z) (tails_cur_2: (@list Z)) ,
  “ (left >= right) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur_2)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= right) ” 
  &&  “ (right <= len) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur_2)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_cur_2)) len x left right ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur_2 )
|--
  EX (tails_cur: (@list Z)) ,
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= len) ” 
  &&  “ (right = left) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_cur)) len x left left ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur )
.

Definition lengthOfLNDS_entail_wit_7 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (tails_cur: (@list Z)) (i: Z) (len: Z) (x: Z) (left: Z) (right: Z) ,
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= len) ” 
  &&  “ (right = left) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_cur)) len x left left ) ”
  &&  (IntArray.full tails_pre numsSize_pre (replace_Znth (left) (x) (tails_cur)) )
  **  (IntArray.full nums_pre numsSize_pre l )
|--
  EX (tails_old: (@list Z)) ,
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_old)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= len) ” 
  &&  “ (right = left) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_old)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_old)) len x left left ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre (app ((sublist (0) (left) (tails_old))) ((cons (x) ((sublist ((left + 1 )) (numsSize_pre) (tails_old)))))) )
.

Definition lengthOfLNDS_entail_wit_8_1 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (tails_old: (@list Z)) (i: Z) (len: Z) (x: Z) (left: Z) (right: Z) ,
  “ (left = len) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_old)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= len) ” 
  &&  “ (right = left) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_old)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_old)) len x left left ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre (app ((sublist (0) (left) (tails_old))) ((cons (x) ((sublist ((left + 1 )) (numsSize_pre) (tails_old)))))) )
|--
  EX (tails_cur: (@list Z)) ,
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ ((len + 1 ) <= (i + 1 )) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= (len + 1 )) ” 
  &&  “ (right = left) ” 
  &&  “ (LNDTailsState l (i + 1 ) (sublist (0) ((len + 1 )) (tails_cur)) (len + 1 ) ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur )
.

Definition lengthOfLNDS_entail_wit_8_2 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (tails_old: (@list Z)) (i: Z) (len: Z) (x: Z) (left: Z) (right: Z) ,
  “ (left <> len) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_old)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= len) ” 
  &&  “ (right = left) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_old)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_old)) len x left left ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre (app ((sublist (0) (left) (tails_old))) ((cons (x) ((sublist ((left + 1 )) (numsSize_pre) (tails_old)))))) )
|--
  EX (tails_cur: (@list Z)) ,
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= (i + 1 )) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= len) ” 
  &&  “ (right = left) ” 
  &&  “ (LNDTailsState l (i + 1 ) (sublist (0) (len) (tails_cur)) len ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur )
.

Definition lengthOfLNDS_entail_wit_9 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (tails_cur_2: (@list Z)) (i: Z) (len: Z) (x: Z) (left: Z) (right: Z) ,
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur_2)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= (i + 1 )) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= len) ” 
  &&  “ (right = left) ” 
  &&  “ (LNDTailsState l (i + 1 ) (sublist (0) (len) (tails_cur_2)) len ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur_2 )
|--
  EX (tails_cur: (@list Z)) ,
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= (i + 1 )) ” 
  &&  “ (LNDTailsState l (i + 1 ) (sublist (0) (len) (tails_cur)) len ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur )
.

Definition lengthOfLNDS_entail_wit_10 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (len: Z) (i: Z) (tails_cur_2: (@list Z)) ,
  “ (i >= numsSize_pre) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur_2)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur_2)) len ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur_2 )
|--
  EX (tails_cur: (@list Z)) ,
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= numsSize_pre) ” 
  &&  “ (LNDSLength l len ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur )
.

Definition lengthOfLNDS_return_wit_1 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (tails_cur: (@list Z)) (len: Z) ,
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= numsSize_pre) ” 
  &&  “ (LNDSLength l len ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur )
|--
  EX (tails_ret: (@list Z)) ,
  “ (LNDSLength l len ) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= numsSize_pre) ” 
  &&  “ ((Zlength (tails_ret)) = numsSize_pre) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_ret )
.

Definition lengthOfLNDS_partial_solve_wit_1 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (len: Z) (i: Z) (tails_cur: (@list Z)) ,
  “ (i < numsSize_pre) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur)) len ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur )
|--
  “ (i < numsSize_pre) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur)) len ) ”
  &&  (((nums_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i nums_pre i 0 numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur )
.

Definition lengthOfLNDS_partial_solve_wit_2 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (tails_cur: (@list Z)) (i: Z) (len: Z) (x: Z) (left: Z) (right: Z) (mid: Z) ,
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < right) ” 
  &&  “ (right <= len) ” 
  &&  “ (left <= mid) ” 
  &&  “ (mid < right) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_cur)) len x left right ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur )
|--
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < right) ” 
  &&  “ (right <= len) ” 
  &&  “ (left <= mid) ” 
  &&  “ (mid < right) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_cur)) len x left right ) ”
  &&  (((tails_pre + (mid * sizeof(INT) ) )) # Int  |-> (Znth mid tails_cur 0))
  **  (IntArray.missing_i tails_pre mid 0 numsSize_pre tails_cur )
  **  (IntArray.full nums_pre numsSize_pre l )
.

Definition lengthOfLNDS_partial_solve_wit_3 := 
forall (tails_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (tails_cur: (@list Z)) (i: Z) (len: Z) (x: Z) (left: Z) (right: Z) ,
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= len) ” 
  &&  “ (right = left) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_cur)) len x left left ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full tails_pre numsSize_pre tails_cur )
|--
  “ (0 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ ((Zlength (tails_cur)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= i) ” 
  &&  “ (x = (Znth i l 0)) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= len) ” 
  &&  “ (right = left) ” 
  &&  “ (LNDTailsState l i (sublist (0) (len) (tails_cur)) len ) ” 
  &&  “ (UpperBoundSearch (sublist (0) (len) (tails_cur)) len x left left ) ”
  &&  (((tails_pre + (left * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i tails_pre left 0 numsSize_pre tails_cur )
  **  (IntArray.full nums_pre numsSize_pre l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_lengthOfLNDS_safety_wit_1 : lengthOfLNDS_safety_wit_1.
Axiom proof_of_lengthOfLNDS_safety_wit_2 : lengthOfLNDS_safety_wit_2.
Axiom proof_of_lengthOfLNDS_safety_wit_3 : lengthOfLNDS_safety_wit_3.
Axiom proof_of_lengthOfLNDS_safety_wit_4 : lengthOfLNDS_safety_wit_4.
Axiom proof_of_lengthOfLNDS_safety_wit_5 : lengthOfLNDS_safety_wit_5.
Axiom proof_of_lengthOfLNDS_safety_wit_6 : lengthOfLNDS_safety_wit_6.
Axiom proof_of_lengthOfLNDS_safety_wit_7 : lengthOfLNDS_safety_wit_7.
Axiom proof_of_lengthOfLNDS_safety_wit_8 : lengthOfLNDS_safety_wit_8.
Axiom proof_of_lengthOfLNDS_safety_wit_9 : lengthOfLNDS_safety_wit_9.
Axiom proof_of_lengthOfLNDS_safety_wit_10 : lengthOfLNDS_safety_wit_10.
Axiom proof_of_lengthOfLNDS_safety_wit_11 : lengthOfLNDS_safety_wit_11.
Axiom proof_of_lengthOfLNDS_safety_wit_12 : lengthOfLNDS_safety_wit_12.
Axiom proof_of_lengthOfLNDS_entail_wit_1 : lengthOfLNDS_entail_wit_1.
Axiom proof_of_lengthOfLNDS_entail_wit_2 : lengthOfLNDS_entail_wit_2.
Axiom proof_of_lengthOfLNDS_entail_wit_3 : lengthOfLNDS_entail_wit_3.
Axiom proof_of_lengthOfLNDS_entail_wit_4 : lengthOfLNDS_entail_wit_4.
Axiom proof_of_lengthOfLNDS_entail_wit_5_1 : lengthOfLNDS_entail_wit_5_1.
Axiom proof_of_lengthOfLNDS_entail_wit_5_2 : lengthOfLNDS_entail_wit_5_2.
Axiom proof_of_lengthOfLNDS_entail_wit_6 : lengthOfLNDS_entail_wit_6.
Axiom proof_of_lengthOfLNDS_entail_wit_7 : lengthOfLNDS_entail_wit_7.
Axiom proof_of_lengthOfLNDS_entail_wit_8_1 : lengthOfLNDS_entail_wit_8_1.
Axiom proof_of_lengthOfLNDS_entail_wit_8_2 : lengthOfLNDS_entail_wit_8_2.
Axiom proof_of_lengthOfLNDS_entail_wit_9 : lengthOfLNDS_entail_wit_9.
Axiom proof_of_lengthOfLNDS_entail_wit_10 : lengthOfLNDS_entail_wit_10.
Axiom proof_of_lengthOfLNDS_return_wit_1 : lengthOfLNDS_return_wit_1.
Axiom proof_of_lengthOfLNDS_partial_solve_wit_1 : lengthOfLNDS_partial_solve_wit_1.
Axiom proof_of_lengthOfLNDS_partial_solve_wit_2 : lengthOfLNDS_partial_solve_wit_2.
Axiom proof_of_lengthOfLNDS_partial_solve_wit_3 : lengthOfLNDS_partial_solve_wit_3.

End VC_Correct.
