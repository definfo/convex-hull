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
Require Import SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack.multiple_knapsack_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function multipleKnapsack -----*)

Definition multipleKnapsack_safety_wit_1 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (qval0: (@list Z)) (qidx0: (@list Z)) (old0: (@list Z)) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (old0)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx0)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval0)) = (capacity_pre + 1 )) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.undef_full dp_pre (capacity_pre + 1 ) )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old0 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx0 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multipleKnapsack_safety_wit_2 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (qval0: (@list Z)) (qidx0: (@list Z)) (old0: (@list Z)) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (dp_l: (@list Z)) ,
  “ (j <= capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = j) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKZeroPrefix dp_l j ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.seg dp_pre 0 j dp_l )
  **  (IntArray.undef_seg dp_pre j (capacity_pre + 1 ) )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old0 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx0 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multipleKnapsack_safety_wit_3 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (qval0: (@list Z)) (qidx0: (@list Z)) (old0: (@list Z)) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (dp_l: (@list Z)) ,
  “ (j <= capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = j) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKZeroPrefix dp_l j ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.seg dp_pre 0 (j + 1 ) (app (dp_l) ((cons (0) (nil)))) )
  **  (IntArray.undef_seg dp_pre (j + 1 ) (capacity_pre + 1 ) )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old0 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx0 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval0 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition multipleKnapsack_safety_wit_4 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (qval0: (@list Z)) (qidx0: (@list Z)) (old0: (@list Z)) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ (MKZeroPrefix dp_l (capacity_pre + 1 ) ) ” 
  &&  “ (MKDPTable weights_l values_l counts_l 0 capacity_pre dp_l ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old0 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx0 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multipleKnapsack_safety_wit_5 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multipleKnapsack_safety_wit_6 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ (j <= capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ (MKCopyPrefix dp_l old_l j capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full old_pre (capacity_pre + 1 ) (replace_Znth (j) ((Znth j dp_l 0)) (old_l)) )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition multipleKnapsack_safety_wit_7 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (old_l: (@list Z)) (qidx_l: (@list Z)) (qval_l: (@list Z)) (i: Z) (w: Z) (v: Z) (cnt: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKCopyPrefix dp_l old_l (capacity_pre + 1 ) capacity_pre ) ” 
  &&  “ (MKItemResidueProgress old_l dp_l 0 w v cnt capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multipleKnapsack_safety_wit_8 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (r: Z) (cnt: Z) (v: Z) (w: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ (r > capacity_pre) ” 
  &&  “ (r < w) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r <= w) ” 
  &&  “ (r <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResidueProgress old_l dp_l r w v cnt capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ False ”
.

Definition multipleKnapsack_safety_wit_9 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (r: Z) (cnt: Z) (v: Z) (w: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ (r <= capacity_pre) ” 
  &&  “ (r < w) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r <= w) ” 
  &&  “ (r <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResidueProgress old_l dp_l r w v cnt capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  ((( &( "head" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multipleKnapsack_safety_wit_10 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (r: Z) (cnt: Z) (v: Z) (w: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ (r <= capacity_pre) ” 
  &&  “ (r < w) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r <= w) ” 
  &&  “ (r <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResidueProgress old_l dp_l r w v cnt capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  ((( &( "tail" ) )) # Int  |->_)
  **  ((( &( "head" ) )) # Int  |-> 0)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multipleKnapsack_safety_wit_11 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (r: Z) (cnt: Z) (v: Z) (w: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ (r <= capacity_pre) ” 
  &&  “ (r < w) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r <= w) ” 
  &&  “ (r <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResidueProgress old_l dp_l r w v cnt capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "tail" ) )) # Int  |-> 0)
  **  ((( &( "head" ) )) # Int  |-> 0)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multipleKnapsack_safety_wit_12 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ (pos <= capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= (capacity_pre + w )) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKResidueLoopState old_l dp_l qidx_l qval_l r w v cnt k head tail capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  ((( &( "current" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ (((Znth pos old_l 0) - (k * v ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth pos old_l 0) - (k * v ) )) ”
.

Definition multipleKnapsack_safety_wit_13 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ (pos <= capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= (capacity_pre + w )) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKResidueLoopState old_l dp_l qidx_l qval_l r w v cnt k head tail capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  ((( &( "current" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ ((k * v ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k * v )) ”
.

Definition multipleKnapsack_safety_wit_14 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueDropLoopState old_l qidx_l qval_l head tail r w v cnt k capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ ((k - cnt ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - cnt )) ”
.

Definition multipleKnapsack_safety_wit_15 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ ((Znth head qidx_l 0) < (k - cnt )) ” 
  &&  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueDropLoopState old_l qidx_l qval_l head tail r w v cnt k capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ ((head + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (head + 1 )) ”
.

Definition multipleKnapsack_safety_wit_16 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ ((head < tail) -> ((0 <= (tail - 1 )) /\ ((tail - 1 ) < (capacity_pre + 1 )))) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingState old_l qidx_l qval_l head tail r w v cnt k capacity_pre current ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ ((tail - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (tail - 1 )) ”
.

Definition multipleKnapsack_safety_wit_17 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ ((head < tail) -> ((0 <= (tail - 1 )) /\ ((tail - 1 ) < (capacity_pre + 1 )))) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingState old_l qidx_l qval_l head tail r w v cnt k capacity_pre current ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition multipleKnapsack_safety_wit_18 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ ((Znth (tail - 1 ) qval_l 0) <= current) ” 
  &&  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ ((head < tail) -> ((0 <= (tail - 1 )) /\ ((tail - 1 ) < (capacity_pre + 1 )))) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingState old_l qidx_l qval_l head tail r w v cnt k capacity_pre current ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
|--
  “ ((tail - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (tail - 1 )) ”
.

Definition multipleKnapsack_safety_wit_19 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ ((Znth (tail - 1 ) qval_l 0) > current) ” 
  &&  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ ((head < tail) -> ((0 <= (tail - 1 )) /\ ((tail - 1 ) < (capacity_pre + 1 )))) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingState old_l qidx_l qval_l head tail r w v cnt k capacity_pre current ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full q_val_pre (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
|--
  “ ((tail + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (tail + 1 )) ”
.

Definition multipleKnapsack_safety_wit_20 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ (head >= tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ ((head < tail) -> ((0 <= (tail - 1 )) /\ ((tail - 1 ) < (capacity_pre + 1 )))) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingState old_l qidx_l qval_l head tail r w v cnt k capacity_pre current ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full q_val_pre (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
|--
  “ ((tail + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (tail + 1 )) ”
.

Definition multipleKnapsack_safety_wit_21 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (old_l: (@list Z)) (qidx_l: (@list Z)) (qval_l: (@list Z)) (i: Z) (r: Z) (w: Z) (v: Z) (cnt: Z) (pos: Z) (k: Z) (current: Z) (head: Z) (tail: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head < tail) ” 
  &&  “ (tail <= (k + 1 )) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueState old_l qidx_l qval_l head tail r w v cnt (k + 1 ) capacity_pre ) ” 
  &&  “ (MKTransitionValue old_l w v cnt capacity_pre pos ((Znth head qval_l 0) + (k * v ) ) ) ” 
  &&  “ (0 <= ((Znth head qval_l 0) + (k * v ) )) ” 
  &&  “ (((Znth head qval_l 0) + (k * v ) ) <= 1000000) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
|--
  “ (((Znth head qval_l 0) + (k * v ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth head qval_l 0) + (k * v ) )) ”
.

Definition multipleKnapsack_safety_wit_22 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (old_l: (@list Z)) (qidx_l: (@list Z)) (qval_l: (@list Z)) (i: Z) (r: Z) (w: Z) (v: Z) (cnt: Z) (pos: Z) (k: Z) (current: Z) (head: Z) (tail: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head < tail) ” 
  &&  “ (tail <= (k + 1 )) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueState old_l qidx_l qval_l head tail r w v cnt (k + 1 ) capacity_pre ) ” 
  &&  “ (MKTransitionValue old_l w v cnt capacity_pre pos ((Znth head qval_l 0) + (k * v ) ) ) ” 
  &&  “ (0 <= ((Znth head qval_l 0) + (k * v ) )) ” 
  &&  “ (((Znth head qval_l 0) + (k * v ) ) <= 1000000) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
|--
  “ ((k * v ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k * v )) ”
.

Definition multipleKnapsack_safety_wit_23 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (old_l: (@list Z)) (qidx_l: (@list Z)) (qval_l: (@list Z)) (i: Z) (r: Z) (w: Z) (v: Z) (cnt: Z) (pos: Z) (k: Z) (current: Z) (head: Z) (tail: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head < tail) ” 
  &&  “ (tail <= (k + 1 )) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueState old_l qidx_l qval_l head tail r w v cnt (k + 1 ) capacity_pre ) ” 
  &&  “ (MKTransitionValue old_l w v cnt capacity_pre pos ((Znth head qval_l 0) + (k * v ) ) ) ” 
  &&  “ (0 <= ((Znth head qval_l 0) + (k * v ) )) ” 
  &&  “ (((Znth head qval_l 0) + (k * v ) ) <= 1000000) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full dp_pre (capacity_pre + 1 ) (replace_Znth (pos) (((Znth head qval_l 0) + (k * v ) )) (dp_l)) )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition multipleKnapsack_safety_wit_24 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (old_l: (@list Z)) (qidx_l: (@list Z)) (qval_l: (@list Z)) (i: Z) (r: Z) (w: Z) (v: Z) (cnt: Z) (pos: Z) (k: Z) (current: Z) (head: Z) (tail: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head < tail) ” 
  &&  “ (tail <= (k + 1 )) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueState old_l qidx_l qval_l head tail r w v cnt (k + 1 ) capacity_pre ) ” 
  &&  “ (MKTransitionValue old_l w v cnt capacity_pre pos ((Znth head qval_l 0) + (k * v ) ) ) ” 
  &&  “ (0 <= ((Znth head qval_l 0) + (k * v ) )) ” 
  &&  “ (((Znth head qval_l 0) + (k * v ) ) <= 1000000) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full dp_pre (capacity_pre + 1 ) (replace_Znth (pos) (((Znth head qval_l 0) + (k * v ) )) (dp_l)) )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
|--
  “ ((pos + w ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos + w )) ”
.

Definition multipleKnapsack_safety_wit_25 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (old_l: (@list Z)) (qidx_l: (@list Z)) (qval_l: (@list Z)) (i: Z) (r: Z) (w: Z) (v: Z) (cnt: Z) (k: Z) (head: Z) (tail: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResidueProgress old_l dp_l (r + 1 ) w v cnt capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ ((r + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition multipleKnapsack_safety_wit_26 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (old_l: (@list Z)) (qidx_l: (@list Z)) (qval_l: (@list Z)) (i: Z) (w: Z) (v: Z) (cnt: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (MKDPTable weights_l values_l counts_l (i + 1 ) capacity_pre dp_l ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "old" ) )) # Ptr  |-> old_pre)
  **  ((( &( "q_idx" ) )) # Ptr  |-> q_idx_pre)
  **  ((( &( "q_val" ) )) # Ptr  |-> q_val_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition multipleKnapsack_entail_wit_1 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (qval0: (@list Z)) (qidx0: (@list Z)) (old0: (@list Z)) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (old0)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx0)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval0)) = (capacity_pre + 1 )) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l 0)) /\ ((Znth idx_2 weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx_2 values_l 0))) /\ ((Znth idx_2 values_l 0) <= 1000)) /\ (0 <= (Znth idx_2 counts_l 0))) /\ ((Znth idx_2 counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.undef_full dp_pre (capacity_pre + 1 ) )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old0 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx0 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval0 )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (capacity_pre + 1 )) ” 
  &&  “ (MKZeroPrefix dp_l 0 ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.seg dp_pre 0 0 dp_l )
  **  (IntArray.undef_seg dp_pre 0 (capacity_pre + 1 ) )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old0 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx0 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval0 )
.

Definition multipleKnapsack_entail_wit_2 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (qval0: (@list Z)) (qidx0: (@list Z)) (old0: (@list Z)) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (dp_l_2: (@list Z)) ,
  “ (j <= capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = j) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKZeroPrefix dp_l_2 j ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.seg dp_pre 0 (j + 1 ) (app (dp_l_2) ((cons (0) (nil)))) )
  **  (IntArray.undef_seg dp_pre (j + 1 ) (capacity_pre + 1 ) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old0 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx0 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval0 )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (j + 1 )) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (MKZeroPrefix dp_l (j + 1 ) ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.seg dp_pre 0 (j + 1 ) dp_l )
  **  (IntArray.undef_seg dp_pre (j + 1 ) (capacity_pre + 1 ) )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old0 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx0 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval0 )
.

Definition multipleKnapsack_entail_wit_3 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (qval0: (@list Z)) (qidx0: (@list Z)) (old0: (@list Z)) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (dp_l_2: (@list Z)) ,
  “ (j > capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = j) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKZeroPrefix dp_l_2 j ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l 0)) /\ ((Znth idx_2 weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx_2 values_l 0))) /\ ((Znth idx_2 values_l 0) <= 1000)) /\ (0 <= (Znth idx_2 counts_l 0))) /\ ((Znth idx_2 counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.seg dp_pre 0 j dp_l_2 )
  **  (IntArray.undef_seg dp_pre j (capacity_pre + 1 ) )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old0 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx0 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval0 )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ (MKZeroPrefix dp_l (capacity_pre + 1 ) ) ” 
  &&  “ (MKDPTable weights_l values_l counts_l 0 capacity_pre dp_l ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old0 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx0 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval0 )
.

Definition multipleKnapsack_entail_wit_4 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (qval0: (@list Z)) (qidx0: (@list Z)) (old0: (@list Z)) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ (MKZeroPrefix dp_l_2 (capacity_pre + 1 ) ) ” 
  &&  “ (MKDPTable weights_l values_l counts_l 0 capacity_pre dp_l_2 ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l 0)) /\ ((Znth idx_2 weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx_2 values_l 0))) /\ ((Znth idx_2 values_l 0) <= 1000)) /\ (0 <= (Znth idx_2 counts_l 0))) /\ ((Znth idx_2 counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old0 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx0 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval0 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (MKDPTable weights_l values_l counts_l 0 capacity_pre dp_l ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_entail_wit_5 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre dp_l_2 ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l 0)) /\ ((Znth idx_2 weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx_2 values_l 0))) /\ ((Znth idx_2 values_l 0) <= 1000)) /\ (0 <= (Znth idx_2 counts_l 0))) /\ ((Znth idx_2 counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l_2 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ (MKCopyPrefix dp_l old_l 0 capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_entail_wit_6 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) ,
  “ (j <= capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre dp_l_2 ) ” 
  &&  “ (MKCopyPrefix dp_l_2 old_l_2 j capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full old_pre (capacity_pre + 1 ) (replace_Znth (j) ((Znth j dp_l_2 0)) (old_l_2)) )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l_2 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ (MKCopyPrefix dp_l old_l (j + 1 ) capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_entail_wit_7 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) ,
  “ (j > capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre dp_l_2 ) ” 
  &&  “ (MKCopyPrefix dp_l_2 old_l_2 j capacity_pre ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l 0)) /\ ((Znth idx_2 weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx_2 values_l 0))) /\ ((Znth idx_2 values_l 0) <= 1000)) /\ (0 <= (Znth idx_2 counts_l 0))) /\ ((Znth idx_2 counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l_2 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Znth i weights_l 0) = (Znth i weights_l 0)) ” 
  &&  “ ((Znth i values_l 0) = (Znth i values_l 0)) ” 
  &&  “ ((Znth i counts_l 0) = (Znth i counts_l 0)) ” 
  &&  “ (1 <= (Znth i weights_l 0)) ” 
  &&  “ ((Znth i weights_l 0) <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= (Znth i values_l 0)) ” 
  &&  “ ((Znth i values_l 0) <= 1000) ” 
  &&  “ (0 <= (Znth i counts_l 0)) ” 
  &&  “ ((Znth i counts_l 0) <= capacity_pre) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l (Znth i weights_l 0) (Znth i values_l 0) (Znth i counts_l 0) capacity_pre ) ” 
  &&  “ (MKCopyPrefix dp_l old_l (capacity_pre + 1 ) capacity_pre ) ” 
  &&  “ (MKItemResidueProgress old_l dp_l 0 (Znth i weights_l 0) (Znth i values_l 0) (Znth i counts_l 0) capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_entail_wit_8 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (old_l_2: (@list Z)) (qidx_l_2: (@list Z)) (qval_l_2: (@list Z)) (i: Z) (w: Z) (v: Z) (cnt: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre dp_l_2 ) ” 
  &&  “ (MKDPValueBound old_l_2 capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l_2 w v cnt capacity_pre ) ” 
  &&  “ (MKCopyPrefix dp_l_2 old_l_2 (capacity_pre + 1 ) capacity_pre ) ” 
  &&  “ (MKItemResidueProgress old_l_2 dp_l_2 0 w v cnt capacity_pre ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l 0)) /\ ((Znth idx_2 weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx_2 values_l 0))) /\ ((Znth idx_2 values_l 0) <= 1000)) /\ (0 <= (Znth idx_2 counts_l 0))) /\ ((Znth idx_2 counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l_2 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= w) ” 
  &&  “ (0 <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResidueProgress old_l dp_l 0 w v cnt capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_entail_wit_9 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (r: Z) (cnt: Z) (v: Z) (w: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) ,
  “ (r <= capacity_pre) ” 
  &&  “ (r < w) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r <= w) ” 
  &&  “ (r <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l_2 ) ” 
  &&  “ (MKDPValueBound old_l_2 capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l_2 w v cnt capacity_pre ) ” 
  &&  “ (MKItemResidueProgress old_l_2 dp_l_2 r w v cnt capacity_pre ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l 0)) /\ ((Znth idx_2 weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx_2 values_l 0))) /\ ((Znth idx_2 values_l 0) <= 1000)) /\ (0 <= (Znth idx_2 counts_l 0))) /\ ((Znth idx_2 counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l_2 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (r = (r + (0 * w ) )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r <= (capacity_pre + w )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt 0 capacity_pre ) ” 
  &&  “ (MKResidueLoopState old_l dp_l qidx_l qval_l r w v cnt 0 0 0 capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_entail_wit_10 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l: (@list Z)) (dp_l_2: (@list Z)) ,
  “ (pos <= capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= (capacity_pre + w )) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l_2 r w v cnt k capacity_pre ) ” 
  &&  “ (MKResidueLoopState old_l dp_l_2 qidx_l_2 qval_l_2 r w v cnt k head tail capacity_pre ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l 0)) /\ ((Znth idx_2 weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx_2 values_l 0))) /\ ((Znth idx_2 values_l 0) <= 1000)) /\ (0 <= (Znth idx_2 counts_l 0))) /\ ((Znth idx_2 counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l_2 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l_2: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (((Znth pos old_l 0) - (k * v ) ) = ((Znth pos old_l_2 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ (((Znth pos old_l 0) - (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= (((Znth pos old_l 0) - (k * v ) ) + (k * v ) )) ” 
  &&  “ ((((Znth pos old_l 0) - (k * v ) ) + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l_2 ) ” 
  &&  “ (MKDPValueBound old_l_2 capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l_2 w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l_2 dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueDropLoopState old_l_2 qidx_l qval_l head tail r w v cnt k capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_entail_wit_11 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) ,
  “ ((Znth head qidx_l_2 0) < (k - cnt )) ” 
  &&  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l_2 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l_2 ) ” 
  &&  “ (MKDPValueBound old_l_2 capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l_2 w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l_2 dp_l_2 r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueDropLoopState old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l_2 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= (head + 1 )) ” 
  &&  “ ((head + 1 ) <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueDropLoopState old_l qidx_l qval_l (head + 1 ) tail r w v cnt k capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_entail_wit_12_1 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) ,
  “ (head >= tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l_2 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l_2 ) ” 
  &&  “ (MKDPValueBound old_l_2 capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l_2 w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l_2 dp_l_2 r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueDropLoopState old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l 0)) /\ ((Znth idx_2 weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx_2 values_l 0))) /\ ((Znth idx_2 values_l 0) <= 1000)) /\ (0 <= (Znth idx_2 counts_l 0))) /\ ((Znth idx_2 counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l_2 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ ((head < tail) -> ((0 <= (tail - 1 )) /\ ((tail - 1 ) < (capacity_pre + 1 )))) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueAfterDrop old_l qidx_l qval_l head tail r w v cnt k capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_entail_wit_12_2 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) ,
  “ ((Znth head qidx_l_2 0) >= (k - cnt )) ” 
  &&  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l_2 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l_2 ) ” 
  &&  “ (MKDPValueBound old_l_2 capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l_2 w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l_2 dp_l_2 r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueDropLoopState old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l 0)) /\ ((Znth idx_2 weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx_2 values_l 0))) /\ ((Znth idx_2 values_l 0) <= 1000)) /\ (0 <= (Znth idx_2 counts_l 0))) /\ ((Znth idx_2 counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l_2 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ ((head < tail) -> ((0 <= (tail - 1 )) /\ ((tail - 1 ) < (capacity_pre + 1 )))) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueAfterDrop old_l qidx_l qval_l head tail r w v cnt k capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_entail_wit_13 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (old_l_2: (@list Z)) (qidx_l_2: (@list Z)) (qval_l_2: (@list Z)) (i: Z) (r: Z) (w: Z) (v: Z) (cnt: Z) (pos: Z) (k: Z) (current: Z) (head: Z) (tail: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l_2 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ ((head < tail) -> ((0 <= (tail - 1 )) /\ ((tail - 1 ) < (capacity_pre + 1 )))) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l_2 ) ” 
  &&  “ (MKDPValueBound old_l_2 capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l_2 w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l_2 dp_l_2 r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueAfterDrop old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l 0)) /\ ((Znth idx_2 weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx_2 values_l 0))) /\ ((Znth idx_2 values_l 0) <= 1000)) /\ (0 <= (Znth idx_2 counts_l 0))) /\ ((Znth idx_2 counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l_2 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ ((head < tail) -> ((0 <= (tail - 1 )) /\ ((tail - 1 ) < (capacity_pre + 1 )))) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingState old_l qidx_l qval_l head tail r w v cnt k capacity_pre current ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_entail_wit_14 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) ,
  “ ((Znth (tail - 1 ) qval_l_2 0) <= current) ” 
  &&  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l_2 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ ((head < tail) -> ((0 <= (tail - 1 )) /\ ((tail - 1 ) < (capacity_pre + 1 )))) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l_2 ) ” 
  &&  “ (MKDPValueBound old_l_2 capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l_2 w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l_2 dp_l_2 r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingState old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l_2 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l_2 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= (tail - 1 )) ” 
  &&  “ ((tail - 1 ) <= k) ” 
  &&  “ ((tail - 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ ((head < (tail - 1 )) -> ((0 <= ((tail - 1 ) - 1 )) /\ (((tail - 1 ) - 1 ) < (capacity_pre + 1 )))) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingState old_l qidx_l qval_l head (tail - 1 ) r w v cnt k capacity_pre current ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_entail_wit_15_1 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) ,
  “ ((Znth (tail - 1 ) qval_l_2 0) > current) ” 
  &&  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l_2 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ ((head < tail) -> ((0 <= (tail - 1 )) /\ ((tail - 1 ) < (capacity_pre + 1 )))) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l_2 ) ” 
  &&  “ (MKDPValueBound old_l_2 capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l_2 w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l_2 dp_l_2 r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingState old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l 0)) /\ ((Znth idx_2 weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx_2 values_l 0))) /\ ((Znth idx_2 values_l 0) <= 1000)) /\ (0 <= (Znth idx_2 counts_l 0))) /\ ((Znth idx_2 counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full q_val_pre (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l_2)) )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l_2)) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l_2 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head < (tail + 1 )) ” 
  &&  “ ((tail + 1 ) <= (k + 1 )) ” 
  &&  “ ((tail + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueState old_l qidx_l qval_l head (tail + 1 ) r w v cnt (k + 1 ) capacity_pre ) ” 
  &&  “ (MKTransitionValue old_l w v cnt capacity_pre pos ((Znth head qval_l 0) + (k * v ) ) ) ” 
  &&  “ (0 <= ((Znth head qval_l 0) + (k * v ) )) ” 
  &&  “ (((Znth head qval_l 0) + (k * v ) ) <= 1000000) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_entail_wit_15_2 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) ,
  “ (head >= tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l_2 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ ((head < tail) -> ((0 <= (tail - 1 )) /\ ((tail - 1 ) < (capacity_pre + 1 )))) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l_2 ) ” 
  &&  “ (MKDPValueBound old_l_2 capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l_2 w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l_2 dp_l_2 r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingState old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l 0)) /\ ((Znth idx_2 weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx_2 values_l 0))) /\ ((Znth idx_2 values_l 0) <= 1000)) /\ (0 <= (Znth idx_2 counts_l 0))) /\ ((Znth idx_2 counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full q_val_pre (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l_2)) )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l_2)) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l_2 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head < (tail + 1 )) ” 
  &&  “ ((tail + 1 ) <= (k + 1 )) ” 
  &&  “ ((tail + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueState old_l qidx_l qval_l head (tail + 1 ) r w v cnt (k + 1 ) capacity_pre ) ” 
  &&  “ (MKTransitionValue old_l w v cnt capacity_pre pos ((Znth head qval_l 0) + (k * v ) ) ) ” 
  &&  “ (0 <= ((Znth head qval_l 0) + (k * v ) )) ” 
  &&  “ (((Znth head qval_l 0) + (k * v ) ) <= 1000000) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_entail_wit_16 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (old_l_2: (@list Z)) (qidx_l_2: (@list Z)) (qval_l_2: (@list Z)) (i: Z) (r: Z) (w: Z) (v: Z) (cnt: Z) (pos: Z) (k: Z) (current: Z) (head: Z) (tail: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l_2 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head < tail) ” 
  &&  “ (tail <= (k + 1 )) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l_2 ) ” 
  &&  “ (MKDPValueBound old_l_2 capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l_2 w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l_2 dp_l_2 r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueState old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt (k + 1 ) capacity_pre ) ” 
  &&  “ (MKTransitionValue old_l_2 w v cnt capacity_pre pos ((Znth head qval_l_2 0) + (k * v ) ) ) ” 
  &&  “ (0 <= ((Znth head qval_l_2 0) + (k * v ) )) ” 
  &&  “ (((Znth head qval_l_2 0) + (k * v ) ) <= 1000000) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l 0)) /\ ((Znth idx_2 weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx_2 values_l 0))) /\ ((Znth idx_2 values_l 0) <= 1000)) /\ (0 <= (Znth idx_2 counts_l 0))) /\ ((Znth idx_2 counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full dp_pre (capacity_pre + 1 ) (replace_Znth (pos) (((Znth head qval_l_2 0) + (k * v ) )) (dp_l_2)) )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l_2 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l_2 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ ((pos + w ) = (r + ((k + 1 ) * w ) )) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= (pos + w )) ” 
  &&  “ ((pos + w ) <= (capacity_pre + w )) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= (k + 1 )) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt (k + 1 ) capacity_pre ) ” 
  &&  “ (MKResidueLoopState old_l dp_l qidx_l qval_l r w v cnt (k + 1 ) head tail capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_entail_wit_17 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) ,
  “ (pos > capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= (capacity_pre + w )) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l_2 ) ” 
  &&  “ (MKDPValueBound old_l_2 capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l_2 w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l_2 dp_l_2 r w v cnt k capacity_pre ) ” 
  &&  “ (MKResidueLoopState old_l_2 dp_l_2 qidx_l_2 qval_l_2 r w v cnt k head tail capacity_pre ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l 0)) /\ ((Znth idx_2 weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx_2 values_l 0))) /\ ((Znth idx_2 values_l 0) <= 1000)) /\ (0 <= (Znth idx_2 counts_l 0))) /\ ((Znth idx_2 counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l_2 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResidueProgress old_l dp_l (r + 1 ) w v cnt capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_entail_wit_18 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (old_l_2: (@list Z)) (qidx_l_2: (@list Z)) (qval_l_2: (@list Z)) (i: Z) (r: Z) (w: Z) (v: Z) (cnt: Z) (k: Z) (head: Z) (tail: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l_2 ) ” 
  &&  “ (MKDPValueBound old_l_2 capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l_2 w v cnt capacity_pre ) ” 
  &&  “ (MKItemResidueProgress old_l_2 dp_l_2 (r + 1 ) w v cnt capacity_pre ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l 0)) /\ ((Znth idx_2 weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx_2 values_l 0))) /\ ((Znth idx_2 values_l 0) <= 1000)) /\ (0 <= (Znth idx_2 counts_l 0))) /\ ((Znth idx_2 counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l_2 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (0 <= (r + 1 )) ” 
  &&  “ ((r + 1 ) <= w) ” 
  &&  “ ((r + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResidueProgress old_l dp_l (r + 1 ) w v cnt capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_entail_wit_19 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (r: Z) (cnt: Z) (v: Z) (w: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) ,
  “ (r >= w) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r <= w) ” 
  &&  “ (r <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l_2 ) ” 
  &&  “ (MKDPValueBound old_l_2 capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l_2 w v cnt capacity_pre ) ” 
  &&  “ (MKItemResidueProgress old_l_2 dp_l_2 r w v cnt capacity_pre ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l 0)) /\ ((Znth idx_2 weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx_2 values_l 0))) /\ ((Znth idx_2 values_l 0) <= 1000)) /\ (0 <= (Znth idx_2 counts_l 0))) /\ ((Znth idx_2 counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l_2 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (MKDPTable weights_l values_l counts_l (i + 1 ) capacity_pre dp_l ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_entail_wit_20 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (old_l_2: (@list Z)) (qidx_l_2: (@list Z)) (qval_l_2: (@list Z)) (i: Z) (w: Z) (v: Z) (cnt: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (MKDPTable weights_l values_l counts_l (i + 1 ) capacity_pre dp_l_2 ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((((1 <= (Znth idx_2 weights_l 0)) /\ ((Znth idx_2 weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx_2 values_l 0))) /\ ((Znth idx_2 values_l 0) <= 1000)) /\ (0 <= (Znth idx_2 counts_l 0))) /\ ((Znth idx_2 counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l_2 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (MKDPTable weights_l values_l counts_l (i + 1 ) capacity_pre dp_l ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_entail_wit_21 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) ,
  “ (i >= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre dp_l_2 ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l_2 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l n_pre capacity_pre dp_l ) ” 
  &&  “ (MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre (Znth capacity_pre dp_l 0) ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_return_wit_1 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (old_l_2: (@list Z)) (qidx_l_2: (@list Z)) (qval_l_2: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l n_pre capacity_pre dp_l_2 ) ” 
  &&  “ (MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre (Znth capacity_pre dp_l_2 0) ) ”
  &&  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l_2 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre (Znth capacity_pre dp_l_2 0) ) ” 
  &&  “ (MKDPTable weights_l values_l counts_l n_pre capacity_pre dp_l ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_partial_solve_wit_1 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (qval0: (@list Z)) (qidx0: (@list Z)) (old0: (@list Z)) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (dp_l: (@list Z)) ,
  “ (j <= capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = j) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKZeroPrefix dp_l j ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.seg dp_pre 0 j dp_l )
  **  (IntArray.undef_seg dp_pre j (capacity_pre + 1 ) )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old0 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx0 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval0 )
|--
  “ (j <= capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = j) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKZeroPrefix dp_l j ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (((dp_pre + (j * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg dp_pre (j + 1 ) (capacity_pre + 1 ) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.seg dp_pre 0 j dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old0 )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx0 )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval0 )
.

Definition multipleKnapsack_partial_solve_wit_2 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ (j <= capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ (MKCopyPrefix dp_l old_l j capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ (j <= capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ (MKCopyPrefix dp_l old_l j capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (((dp_pre + (j * sizeof(INT) ) )) # Int  |-> (Znth j dp_l 0))
  **  (IntArray.missing_i dp_pre j 0 (capacity_pre + 1 ) dp_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_partial_solve_wit_3 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ (j <= capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ (MKCopyPrefix dp_l old_l j capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ (j <= capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ (MKCopyPrefix dp_l old_l j capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (((old_pre + (j * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i old_pre j 0 (capacity_pre + 1 ) old_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_partial_solve_wit_4 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ (j > capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ (MKCopyPrefix dp_l old_l j capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ (j > capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ (MKCopyPrefix dp_l old_l j capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (((weights_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i weights_l 0))
  **  (IntArray.missing_i weights_pre i 0 n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_partial_solve_wit_5 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ (j > capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ (MKCopyPrefix dp_l old_l j capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ (j > capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ (MKCopyPrefix dp_l old_l j capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (((values_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i values_l 0))
  **  (IntArray.missing_i values_pre i 0 n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_partial_solve_wit_6 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ (j > capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ (MKCopyPrefix dp_l old_l j capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ (j > capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ (MKCopyPrefix dp_l old_l j capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (((counts_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i counts_l 0))
  **  (IntArray.missing_i counts_pre i 0 n_pre counts_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_partial_solve_wit_7 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ (pos <= capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= (capacity_pre + w )) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKResidueLoopState old_l dp_l qidx_l qval_l r w v cnt k head tail capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ (pos <= capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= (capacity_pre + w )) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKResidueLoopState old_l dp_l qidx_l qval_l r w v cnt k head tail capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (((old_pre + (pos * sizeof(INT) ) )) # Int  |-> (Znth pos old_l 0))
  **  (IntArray.missing_i old_pre pos 0 (capacity_pre + 1 ) old_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_partial_solve_wit_8 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueDropLoopState old_l qidx_l qval_l head tail r w v cnt k capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueDropLoopState old_l qidx_l qval_l head tail r w v cnt k capacity_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (((q_idx_pre + (head * sizeof(INT) ) )) # Int  |-> (Znth head qidx_l 0))
  **  (IntArray.missing_i q_idx_pre head 0 (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_partial_solve_wit_9 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ ((head < tail) -> ((0 <= (tail - 1 )) /\ ((tail - 1 ) < (capacity_pre + 1 )))) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingState old_l qidx_l qval_l head tail r w v cnt k capacity_pre current ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ ((head < tail) -> ((0 <= (tail - 1 )) /\ ((tail - 1 ) < (capacity_pre + 1 )))) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingState old_l qidx_l qval_l head tail r w v cnt k capacity_pre current ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (((q_val_pre + ((tail - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (tail - 1 ) qval_l 0))
  **  (IntArray.missing_i q_val_pre (tail - 1 ) 0 (capacity_pre + 1 ) qval_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
.

Definition multipleKnapsack_partial_solve_wit_10 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ ((Znth (tail - 1 ) qval_l 0) > current) ” 
  &&  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ ((head < tail) -> ((0 <= (tail - 1 )) /\ ((tail - 1 ) < (capacity_pre + 1 )))) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingState old_l qidx_l qval_l head tail r w v cnt k capacity_pre current ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
|--
  “ ((Znth (tail - 1 ) qval_l 0) > current) ” 
  &&  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ ((head < tail) -> ((0 <= (tail - 1 )) /\ ((tail - 1 ) < (capacity_pre + 1 )))) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingState old_l qidx_l qval_l head tail r w v cnt k capacity_pre current ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (((q_idx_pre + (tail * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i q_idx_pre tail 0 (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
.

Definition multipleKnapsack_partial_solve_wit_11 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ (head >= tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ ((head < tail) -> ((0 <= (tail - 1 )) /\ ((tail - 1 ) < (capacity_pre + 1 )))) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingState old_l qidx_l qval_l head tail r w v cnt k capacity_pre current ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ (head >= tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ ((head < tail) -> ((0 <= (tail - 1 )) /\ ((tail - 1 ) < (capacity_pre + 1 )))) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingState old_l qidx_l qval_l head tail r w v cnt k capacity_pre current ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (((q_idx_pre + (tail * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i q_idx_pre tail 0 (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Definition multipleKnapsack_partial_solve_wit_12 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ (head >= tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ ((head < tail) -> ((0 <= (tail - 1 )) /\ ((tail - 1 ) < (capacity_pre + 1 )))) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingState old_l qidx_l qval_l head tail r w v cnt k capacity_pre current ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full q_idx_pre (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ (head >= tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ ((head < tail) -> ((0 <= (tail - 1 )) /\ ((tail - 1 ) < (capacity_pre + 1 )))) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingState old_l qidx_l qval_l head tail r w v cnt k capacity_pre current ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (((q_val_pre + (tail * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i q_val_pre tail 0 (capacity_pre + 1 ) qval_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
.

Definition multipleKnapsack_partial_solve_wit_13 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) ,
  “ ((Znth (tail - 1 ) qval_l 0) > current) ” 
  &&  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ ((head < tail) -> ((0 <= (tail - 1 )) /\ ((tail - 1 ) < (capacity_pre + 1 )))) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingState old_l qidx_l qval_l head tail r w v cnt k capacity_pre current ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full q_idx_pre (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
|--
  “ ((Znth (tail - 1 ) qval_l 0) > current) ” 
  &&  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ ((head < tail) -> ((0 <= (tail - 1 )) /\ ((tail - 1 ) < (capacity_pre + 1 )))) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingState old_l qidx_l qval_l head tail r w v cnt k capacity_pre current ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (((q_val_pre + (tail * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i q_val_pre tail 0 (capacity_pre + 1 ) qval_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
.

Definition multipleKnapsack_partial_solve_wit_14 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (old_l: (@list Z)) (qidx_l: (@list Z)) (qval_l: (@list Z)) (i: Z) (r: Z) (w: Z) (v: Z) (cnt: Z) (pos: Z) (k: Z) (current: Z) (head: Z) (tail: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head < tail) ” 
  &&  “ (tail <= (k + 1 )) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueState old_l qidx_l qval_l head tail r w v cnt (k + 1 ) capacity_pre ) ” 
  &&  “ (MKTransitionValue old_l w v cnt capacity_pre pos ((Znth head qval_l 0) + (k * v ) ) ) ” 
  &&  “ (0 <= ((Znth head qval_l 0) + (k * v ) )) ” 
  &&  “ (((Znth head qval_l 0) + (k * v ) ) <= 1000000) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head < tail) ” 
  &&  “ (tail <= (k + 1 )) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueState old_l qidx_l qval_l head tail r w v cnt (k + 1 ) capacity_pre ) ” 
  &&  “ (MKTransitionValue old_l w v cnt capacity_pre pos ((Znth head qval_l 0) + (k * v ) ) ) ” 
  &&  “ (0 <= ((Znth head qval_l 0) + (k * v ) )) ” 
  &&  “ (((Znth head qval_l 0) + (k * v ) ) <= 1000000) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (((q_val_pre + (head * sizeof(INT) ) )) # Int  |-> (Znth head qval_l 0))
  **  (IntArray.missing_i q_val_pre head 0 (capacity_pre + 1 ) qval_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
.

Definition multipleKnapsack_partial_solve_wit_15 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (old_l: (@list Z)) (qidx_l: (@list Z)) (qval_l: (@list Z)) (i: Z) (r: Z) (w: Z) (v: Z) (cnt: Z) (pos: Z) (k: Z) (current: Z) (head: Z) (tail: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head < tail) ” 
  &&  “ (tail <= (k + 1 )) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueState old_l qidx_l qval_l head tail r w v cnt (k + 1 ) capacity_pre ) ” 
  &&  “ (MKTransitionValue old_l w v cnt capacity_pre pos ((Znth head qval_l 0) + (k * v ) ) ) ” 
  &&  “ (0 <= ((Znth head qval_l 0) + (k * v ) )) ” 
  &&  “ (((Znth head qval_l 0) + (k * v ) ) <= 1000000) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head < tail) ” 
  &&  “ (tail <= (k + 1 )) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (MKDPValueBound old_l capacity_pre ) ” 
  &&  “ (MKTransitionValueBound old_l w v cnt capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixProgress old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueState old_l qidx_l qval_l head tail r w v cnt (k + 1 ) capacity_pre ) ” 
  &&  “ (MKTransitionValue old_l w v cnt capacity_pre pos ((Znth head qval_l 0) + (k * v ) ) ) ” 
  &&  “ (0 <= ((Znth head qval_l 0) + (k * v ) )) ” 
  &&  “ (((Znth head qval_l 0) + (k * v ) ) <= 1000000) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((((((1 <= (Znth idx weights_l 0)) /\ ((Znth idx weights_l 0) <= (capacity_pre + 1 ))) /\ (0 <= (Znth idx values_l 0))) /\ ((Znth idx values_l 0) <= 1000)) /\ (0 <= (Znth idx counts_l 0))) /\ ((Znth idx counts_l 0) <= capacity_pre))) ”
  &&  (((dp_pre + (pos * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i dp_pre pos 0 (capacity_pre + 1 ) dp_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
.

Definition multipleKnapsack_partial_solve_wit_16 := 
forall (q_val_pre: Z) (q_idx_pre: Z) (old_pre: Z) (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (old_l: (@list Z)) (qidx_l: (@list Z)) (qval_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l n_pre capacity_pre dp_l ) ” 
  &&  “ (MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre (Znth capacity_pre dp_l 0) ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full dp_pre (capacity_pre + 1 ) dp_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (MKDPTable weights_l values_l counts_l n_pre capacity_pre dp_l ) ” 
  &&  “ (MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre (Znth capacity_pre dp_l 0) ) ”
  &&  (((dp_pre + (capacity_pre * sizeof(INT) ) )) # Int  |-> (Znth capacity_pre dp_l 0))
  **  (IntArray.missing_i dp_pre capacity_pre 0 (capacity_pre + 1 ) dp_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full old_pre (capacity_pre + 1 ) old_l )
  **  (IntArray.full q_idx_pre (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full q_val_pre (capacity_pre + 1 ) qval_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_multipleKnapsack_safety_wit_1 : multipleKnapsack_safety_wit_1.
Axiom proof_of_multipleKnapsack_safety_wit_2 : multipleKnapsack_safety_wit_2.
Axiom proof_of_multipleKnapsack_safety_wit_3 : multipleKnapsack_safety_wit_3.
Axiom proof_of_multipleKnapsack_safety_wit_4 : multipleKnapsack_safety_wit_4.
Axiom proof_of_multipleKnapsack_safety_wit_5 : multipleKnapsack_safety_wit_5.
Axiom proof_of_multipleKnapsack_safety_wit_6 : multipleKnapsack_safety_wit_6.
Axiom proof_of_multipleKnapsack_safety_wit_7 : multipleKnapsack_safety_wit_7.
Axiom proof_of_multipleKnapsack_safety_wit_8 : multipleKnapsack_safety_wit_8.
Axiom proof_of_multipleKnapsack_safety_wit_9 : multipleKnapsack_safety_wit_9.
Axiom proof_of_multipleKnapsack_safety_wit_10 : multipleKnapsack_safety_wit_10.
Axiom proof_of_multipleKnapsack_safety_wit_11 : multipleKnapsack_safety_wit_11.
Axiom proof_of_multipleKnapsack_safety_wit_12 : multipleKnapsack_safety_wit_12.
Axiom proof_of_multipleKnapsack_safety_wit_13 : multipleKnapsack_safety_wit_13.
Axiom proof_of_multipleKnapsack_safety_wit_14 : multipleKnapsack_safety_wit_14.
Axiom proof_of_multipleKnapsack_safety_wit_15 : multipleKnapsack_safety_wit_15.
Axiom proof_of_multipleKnapsack_safety_wit_16 : multipleKnapsack_safety_wit_16.
Axiom proof_of_multipleKnapsack_safety_wit_17 : multipleKnapsack_safety_wit_17.
Axiom proof_of_multipleKnapsack_safety_wit_18 : multipleKnapsack_safety_wit_18.
Axiom proof_of_multipleKnapsack_safety_wit_19 : multipleKnapsack_safety_wit_19.
Axiom proof_of_multipleKnapsack_safety_wit_20 : multipleKnapsack_safety_wit_20.
Axiom proof_of_multipleKnapsack_safety_wit_21 : multipleKnapsack_safety_wit_21.
Axiom proof_of_multipleKnapsack_safety_wit_22 : multipleKnapsack_safety_wit_22.
Axiom proof_of_multipleKnapsack_safety_wit_23 : multipleKnapsack_safety_wit_23.
Axiom proof_of_multipleKnapsack_safety_wit_24 : multipleKnapsack_safety_wit_24.
Axiom proof_of_multipleKnapsack_safety_wit_25 : multipleKnapsack_safety_wit_25.
Axiom proof_of_multipleKnapsack_safety_wit_26 : multipleKnapsack_safety_wit_26.
Axiom proof_of_multipleKnapsack_entail_wit_1 : multipleKnapsack_entail_wit_1.
Axiom proof_of_multipleKnapsack_entail_wit_2 : multipleKnapsack_entail_wit_2.
Axiom proof_of_multipleKnapsack_entail_wit_3 : multipleKnapsack_entail_wit_3.
Axiom proof_of_multipleKnapsack_entail_wit_4 : multipleKnapsack_entail_wit_4.
Axiom proof_of_multipleKnapsack_entail_wit_5 : multipleKnapsack_entail_wit_5.
Axiom proof_of_multipleKnapsack_entail_wit_6 : multipleKnapsack_entail_wit_6.
Axiom proof_of_multipleKnapsack_entail_wit_7 : multipleKnapsack_entail_wit_7.
Axiom proof_of_multipleKnapsack_entail_wit_8 : multipleKnapsack_entail_wit_8.
Axiom proof_of_multipleKnapsack_entail_wit_9 : multipleKnapsack_entail_wit_9.
Axiom proof_of_multipleKnapsack_entail_wit_10 : multipleKnapsack_entail_wit_10.
Axiom proof_of_multipleKnapsack_entail_wit_11 : multipleKnapsack_entail_wit_11.
Axiom proof_of_multipleKnapsack_entail_wit_12_1 : multipleKnapsack_entail_wit_12_1.
Axiom proof_of_multipleKnapsack_entail_wit_12_2 : multipleKnapsack_entail_wit_12_2.
Axiom proof_of_multipleKnapsack_entail_wit_13 : multipleKnapsack_entail_wit_13.
Axiom proof_of_multipleKnapsack_entail_wit_14 : multipleKnapsack_entail_wit_14.
Axiom proof_of_multipleKnapsack_entail_wit_15_1 : multipleKnapsack_entail_wit_15_1.
Axiom proof_of_multipleKnapsack_entail_wit_15_2 : multipleKnapsack_entail_wit_15_2.
Axiom proof_of_multipleKnapsack_entail_wit_16 : multipleKnapsack_entail_wit_16.
Axiom proof_of_multipleKnapsack_entail_wit_17 : multipleKnapsack_entail_wit_17.
Axiom proof_of_multipleKnapsack_entail_wit_18 : multipleKnapsack_entail_wit_18.
Axiom proof_of_multipleKnapsack_entail_wit_19 : multipleKnapsack_entail_wit_19.
Axiom proof_of_multipleKnapsack_entail_wit_20 : multipleKnapsack_entail_wit_20.
Axiom proof_of_multipleKnapsack_entail_wit_21 : multipleKnapsack_entail_wit_21.
Axiom proof_of_multipleKnapsack_return_wit_1 : multipleKnapsack_return_wit_1.
Axiom proof_of_multipleKnapsack_partial_solve_wit_1 : multipleKnapsack_partial_solve_wit_1.
Axiom proof_of_multipleKnapsack_partial_solve_wit_2 : multipleKnapsack_partial_solve_wit_2.
Axiom proof_of_multipleKnapsack_partial_solve_wit_3 : multipleKnapsack_partial_solve_wit_3.
Axiom proof_of_multipleKnapsack_partial_solve_wit_4 : multipleKnapsack_partial_solve_wit_4.
Axiom proof_of_multipleKnapsack_partial_solve_wit_5 : multipleKnapsack_partial_solve_wit_5.
Axiom proof_of_multipleKnapsack_partial_solve_wit_6 : multipleKnapsack_partial_solve_wit_6.
Axiom proof_of_multipleKnapsack_partial_solve_wit_7 : multipleKnapsack_partial_solve_wit_7.
Axiom proof_of_multipleKnapsack_partial_solve_wit_8 : multipleKnapsack_partial_solve_wit_8.
Axiom proof_of_multipleKnapsack_partial_solve_wit_9 : multipleKnapsack_partial_solve_wit_9.
Axiom proof_of_multipleKnapsack_partial_solve_wit_10 : multipleKnapsack_partial_solve_wit_10.
Axiom proof_of_multipleKnapsack_partial_solve_wit_11 : multipleKnapsack_partial_solve_wit_11.
Axiom proof_of_multipleKnapsack_partial_solve_wit_12 : multipleKnapsack_partial_solve_wit_12.
Axiom proof_of_multipleKnapsack_partial_solve_wit_13 : multipleKnapsack_partial_solve_wit_13.
Axiom proof_of_multipleKnapsack_partial_solve_wit_14 : multipleKnapsack_partial_solve_wit_14.
Axiom proof_of_multipleKnapsack_partial_solve_wit_15 : multipleKnapsack_partial_solve_wit_15.
Axiom proof_of_multipleKnapsack_partial_solve_wit_16 : multipleKnapsack_partial_solve_wit_16.

End VC_Correct.
