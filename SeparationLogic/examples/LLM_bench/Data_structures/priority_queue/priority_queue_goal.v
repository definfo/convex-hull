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
Require Import SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function push -----*)

Definition push_safety_wit_1 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (l_cur: (@list Z)) (child: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur n_pre child x_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_cur 0)) /\ ((Znth idx l_cur 0) <= INT_MAX))) ”
  &&  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_cur )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition push_safety_wit_2 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (l_cur: (@list Z)) (child: Z) ,
  “ (child > 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur n_pre child x_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_cur 0)) /\ ((Znth idx l_cur 0) <= INT_MAX))) ”
  &&  ((( &( "parent" ) )) # Int  |->_)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_cur )
|--
  “ (((child - 1 ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition push_safety_wit_3 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (l_cur: (@list Z)) (child: Z) ,
  “ (child > 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur n_pre child x_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_cur 0)) /\ ((Znth idx l_cur 0) <= INT_MAX))) ”
  &&  ((( &( "parent" ) )) # Int  |->_)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_cur )
|--
  “ ((child - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (child - 1 )) ”
.

Definition push_safety_wit_4 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (l_cur: (@list Z)) (child: Z) ,
  “ (child > 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur n_pre child x_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_cur 0)) /\ ((Znth idx l_cur 0) <= INT_MAX))) ”
  &&  ((( &( "parent" ) )) # Int  |->_)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_cur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition push_safety_wit_5 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (l_cur: (@list Z)) (child: Z) ,
  “ (child > 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur n_pre child x_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_cur 0)) /\ ((Znth idx l_cur 0) <= INT_MAX))) ”
  &&  ((( &( "parent" ) )) # Int  |->_)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_cur )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition push_entail_wit_1 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (INT_MIN <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (MaxHeapPrefix l n_pre ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre (n_pre + 1 ) (replace_Znth (n_pre) (x_pre) (l)) )
|--
  EX (l_cur: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur n_pre n_pre x_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_cur 0)) /\ ((Znth idx l_cur 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_cur )
.

Definition push_entail_wit_2 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (l_cur_2: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur_2 n_pre n_pre x_pre ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_2 l_cur_2 0)) /\ ((Znth idx_2 l_cur_2 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_cur_2 )
|--
  EX (l_cur: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur n_pre n_pre x_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_cur 0)) /\ ((Znth idx l_cur 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_cur )
.

Definition push_entail_wit_3 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (l_cur_2: (@list Z)) (child: Z) ,
  “ (child > 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur_2 n_pre child x_pre ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_2 l_cur_2 0)) /\ ((Znth idx_2 l_cur_2 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_cur_2 )
|--
  EX (l_cur: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= ((child - 1 ) ÷ 2 )) ” 
  &&  “ (((child - 1 ) ÷ 2 ) < child) ” 
  &&  “ (((child - 1 ) ÷ 2 ) <= n_pre) ” 
  &&  “ (((child - 1 ) ÷ 2 ) = (HeapParent (child))) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur n_pre child x_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_cur 0)) /\ ((Znth idx l_cur 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_cur )
.

Definition push_entail_wit_4 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (l_cur_2: (@list Z)) (child: Z) (parent: Z) ,
  “ ((Znth (parent - 0 ) l_cur_2 0) >= (Znth (child - 0 ) l_cur_2 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (HeapParent (child))) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur_2 n_pre child x_pre ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_2 l_cur_2 0)) /\ ((Znth idx_2 l_cur_2 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_cur_2 )
|--
  EX (l_cur: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (HeapParent (child))) ” 
  &&  “ ((Znth parent l_cur 0) >= (Znth child l_cur 0)) ” 
  &&  “ (PushResult l l_cur n_pre x_pre ) ” 
  &&  “ (PriorityQueuePrefix l_cur (n_pre + 1 ) ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_cur 0)) /\ ((Znth idx l_cur 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_cur )
.

Definition push_entail_wit_5 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (l_cur: (@list Z)) (child: Z) (parent: Z) ,
  “ ((Znth (parent - 0 ) l_cur 0) < (Znth (child - 0 ) l_cur 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (HeapParent (child))) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur n_pre child x_pre ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_2 l_cur 0)) /\ ((Znth idx_2 l_cur 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre (n_pre + 1 ) (replace_Znth (child) ((Znth (parent - 0 ) l_cur 0)) ((replace_Znth (parent) ((Znth (child - 0 ) l_cur 0)) (l_cur)))) )
|--
  EX (l_cur_2: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (HeapParent (child))) ” 
  &&  “ ((Znth (parent - 0 ) l_cur 0) = (Znth child l_cur_2 0)) ” 
  &&  “ (PushLoopState l l_cur_2 n_pre parent x_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_cur_2 0)) /\ ((Znth idx l_cur_2 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_cur_2 )
.

Definition push_entail_wit_6 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (l_cur_2: (@list Z)) (child: Z) (parent: Z) (tmp: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (HeapParent (child))) ” 
  &&  “ (tmp = (Znth child l_cur_2 0)) ” 
  &&  “ (PushLoopState l l_cur_2 n_pre parent x_pre ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_2 l_cur_2 0)) /\ ((Znth idx_2 l_cur_2 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_cur_2 )
|--
  EX (l_cur: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur n_pre parent x_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_cur 0)) /\ ((Znth idx l_cur 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_cur )
.

Definition push_entail_wit_7_1 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (l_cur: (@list Z)) (child: Z) ,
  “ (child <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur n_pre child x_pre ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_2 l_cur 0)) /\ ((Znth idx_2 l_cur 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_cur )
|--
  EX (l_out: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (PushResult l l_out n_pre x_pre ) ” 
  &&  “ (PriorityQueuePrefix l_out (n_pre + 1 ) ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_out 0)) /\ ((Znth idx l_out 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_out )
.

Definition push_entail_wit_7_2 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (l_cur: (@list Z)) (child: Z) (parent: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (HeapParent (child))) ” 
  &&  “ ((Znth parent l_cur 0) >= (Znth child l_cur 0)) ” 
  &&  “ (PushResult l l_cur n_pre x_pre ) ” 
  &&  “ (PriorityQueuePrefix l_cur (n_pre + 1 ) ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_2 l_cur 0)) /\ ((Znth idx_2 l_cur 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_cur )
|--
  EX (l_out: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (PushResult l l_out n_pre x_pre ) ” 
  &&  “ (PriorityQueuePrefix l_out (n_pre + 1 ) ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_out 0)) /\ ((Znth idx l_out 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_out )
.

Definition push_return_wit_1 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (l_out_2: (@list Z)) (child: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (PushResult l l_out_2 n_pre x_pre ) ” 
  &&  “ (PriorityQueuePrefix l_out_2 (n_pre + 1 ) ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_2 l_out_2 0)) /\ ((Znth idx_2 l_out_2 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_out_2 )
|--
  EX (l_out: (@list Z)) ,
  “ (PushResult l l_out n_pre x_pre ) ” 
  &&  “ (PriorityQueuePrefix l_out (n_pre + 1 ) ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_out 0)) /\ ((Znth idx l_out 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_out )
.

Definition push_partial_solve_wit_1 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (INT_MIN <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (MaxHeapPrefix l n_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l 0)) /\ ((Znth idx l 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (n_pre + 1 ) l )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (INT_MIN <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (MaxHeapPrefix l n_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l 0)) /\ ((Znth idx l 0) <= INT_MAX))) ”
  &&  (((heap_pre + (n_pre * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i heap_pre n_pre 0 (n_pre + 1 ) l )
.

Definition push_partial_solve_wit_2 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (l_cur: (@list Z)) (child: Z) (parent: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (HeapParent (child))) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur n_pre child x_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_cur 0)) /\ ((Znth idx l_cur 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_cur )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (HeapParent (child))) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur n_pre child x_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_cur 0)) /\ ((Znth idx l_cur 0) <= INT_MAX))) ”
  &&  (((heap_pre + (parent * sizeof(INT) ) )) # Int  |-> (Znth (parent - 0 ) l_cur 0))
  **  (IntArray.missing_i heap_pre parent 0 (n_pre + 1 ) l_cur )
.

Definition push_partial_solve_wit_3 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (l_cur: (@list Z)) (child: Z) (parent: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (HeapParent (child))) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur n_pre child x_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_cur 0)) /\ ((Znth idx l_cur 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_cur )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (HeapParent (child))) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur n_pre child x_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_cur 0)) /\ ((Znth idx l_cur 0) <= INT_MAX))) ”
  &&  (((heap_pre + (child * sizeof(INT) ) )) # Int  |-> (Znth (child - 0 ) l_cur 0))
  **  (IntArray.missing_i heap_pre child 0 (n_pre + 1 ) l_cur )
.

Definition push_partial_solve_wit_4 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (l_cur: (@list Z)) (child: Z) (parent: Z) ,
  “ ((Znth (parent - 0 ) l_cur 0) < (Znth (child - 0 ) l_cur 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (HeapParent (child))) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur n_pre child x_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_cur 0)) /\ ((Znth idx l_cur 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_cur )
|--
  “ ((Znth (parent - 0 ) l_cur 0) < (Znth (child - 0 ) l_cur 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (HeapParent (child))) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur n_pre child x_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_cur 0)) /\ ((Znth idx l_cur 0) <= INT_MAX))) ”
  &&  (((heap_pre + (parent * sizeof(INT) ) )) # Int  |-> (Znth (parent - 0 ) l_cur 0))
  **  (IntArray.missing_i heap_pre parent 0 (n_pre + 1 ) l_cur )
.

Definition push_partial_solve_wit_5 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (l_cur: (@list Z)) (child: Z) (parent: Z) ,
  “ ((Znth (parent - 0 ) l_cur 0) < (Znth (child - 0 ) l_cur 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (HeapParent (child))) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur n_pre child x_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_cur 0)) /\ ((Znth idx l_cur 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_cur )
|--
  “ ((Znth (parent - 0 ) l_cur 0) < (Znth (child - 0 ) l_cur 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (HeapParent (child))) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur n_pre child x_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_cur 0)) /\ ((Znth idx l_cur 0) <= INT_MAX))) ”
  &&  (((heap_pre + (child * sizeof(INT) ) )) # Int  |-> (Znth (child - 0 ) l_cur 0))
  **  (IntArray.missing_i heap_pre child 0 (n_pre + 1 ) l_cur )
.

Definition push_partial_solve_wit_6 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (l_cur: (@list Z)) (child: Z) (parent: Z) ,
  “ ((Znth (parent - 0 ) l_cur 0) < (Znth (child - 0 ) l_cur 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (HeapParent (child))) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur n_pre child x_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_cur 0)) /\ ((Znth idx l_cur 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (n_pre + 1 ) l_cur )
|--
  “ ((Znth (parent - 0 ) l_cur 0) < (Znth (child - 0 ) l_cur 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (HeapParent (child))) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur n_pre child x_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_cur 0)) /\ ((Znth idx l_cur 0) <= INT_MAX))) ”
  &&  (((heap_pre + (parent * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i heap_pre parent 0 (n_pre + 1 ) l_cur )
.

Definition push_partial_solve_wit_7 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (l_cur: (@list Z)) (child: Z) (parent: Z) ,
  “ ((Znth (parent - 0 ) l_cur 0) < (Znth (child - 0 ) l_cur 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (HeapParent (child))) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur n_pre child x_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_cur 0)) /\ ((Znth idx l_cur 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre (n_pre + 1 ) (replace_Znth (parent) ((Znth (child - 0 ) l_cur 0)) (l_cur)) )
|--
  “ ((Znth (parent - 0 ) l_cur 0) < (Znth (child - 0 ) l_cur 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100000) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (HeapParent (child))) ” 
  &&  “ ((Zlength (l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth n_pre l 0) = x_pre) ” 
  &&  “ (PushLoopState l l_cur n_pre child x_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx l_cur 0)) /\ ((Znth idx l_cur 0) <= INT_MAX))) ”
  &&  (((heap_pre + (child * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i heap_pre child 0 (n_pre + 1 ) (replace_Znth (parent) ((Znth (child - 0 ) l_cur 0)) (l_cur)) )
.

(*----- Function build -----*)

Definition build_safety_wit_1 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx l 0)) /\ ((Znth idx l 0) <= INT_MAX))) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  (IntArray.full heap_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_safety_wit_2 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (i: Z) (x: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (INT_MIN <= x) ” 
  &&  “ (x <= INT_MAX) ” 
  &&  “ (BuildPrefixState l heap_l (i + 1 ) ) ” 
  &&  “ (PriorityQueuePrefix heap_l (i + 1 ) ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx heap_l 0)) /\ ((Znth idx heap_l 0) <= INT_MAX))) ”
  &&  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full heap_pre n_pre heap_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition build_entail_wit_1 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((INT_MIN <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre l )
|--
  EX (heap_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (BuildPrefixState l heap_l 1 ) ” 
  &&  “ (PriorityQueuePrefix heap_l 1 ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx heap_l 0)) /\ ((Znth idx heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
.

Definition build_entail_wit_2 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (BuildPrefixState l heap_l i ) ” 
  &&  “ (PriorityQueuePrefix heap_l i ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((INT_MIN <= (Znth idx_2 heap_l 0)) /\ ((Znth idx_2 heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
|--
  EX (heap_l_2: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Znth i heap_l 0) = (Znth i heap_l_2 0)) ” 
  &&  “ (BuildPrefixState l heap_l_2 i ) ” 
  &&  “ (PriorityQueuePrefix heap_l_2 i ) ” 
  &&  “ (MaxHeapPrefix heap_l_2 i ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx heap_l_2 0)) /\ ((Znth idx heap_l_2 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (heap_l_2)) )
  **  (IntArray.seg heap_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (heap_l_2)) )
.

Definition build_entail_wit_3 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l_2: (@list Z)) (i: Z) (x: Z) (l_out: (@list Z)) ,
  “ (PushResult (sublist (0) ((i + 1 )) (heap_l_2)) l_out i x ) ” 
  &&  “ (PriorityQueuePrefix l_out (i + 1 ) ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < (i + 1 ))) -> ((INT_MIN <= (Znth idx_2 l_out 0)) /\ ((Znth idx_2 l_out 0) <= INT_MAX))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (x = (Znth i heap_l_2 0)) ” 
  &&  “ (BuildPrefixState l heap_l_2 i ) ” 
  &&  “ (PriorityQueuePrefix heap_l_2 i ) ” 
  &&  “ (MaxHeapPrefix heap_l_2 i ) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < n_pre)) -> ((INT_MIN <= (Znth idx_3 heap_l_2 0)) /\ ((Znth idx_3 heap_l_2 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (i + 1 ) l_out )
  **  (IntArray.seg heap_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (heap_l_2)) )
|--
  EX (heap_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (INT_MIN <= x) ” 
  &&  “ (x <= INT_MAX) ” 
  &&  “ (BuildPrefixState l heap_l (i + 1 ) ) ” 
  &&  “ (PriorityQueuePrefix heap_l (i + 1 ) ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx heap_l 0)) /\ ((Znth idx heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
.

Definition build_entail_wit_4 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l_2: (@list Z)) (i: Z) (x: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (INT_MIN <= x) ” 
  &&  “ (x <= INT_MAX) ” 
  &&  “ (BuildPrefixState l heap_l_2 (i + 1 ) ) ” 
  &&  “ (PriorityQueuePrefix heap_l_2 (i + 1 ) ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((INT_MIN <= (Znth idx_2 heap_l_2 0)) /\ ((Znth idx_2 heap_l_2 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l_2 )
|--
  EX (heap_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (BuildPrefixState l heap_l (i + 1 ) ) ” 
  &&  “ (PriorityQueuePrefix heap_l (i + 1 ) ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx heap_l 0)) /\ ((Znth idx heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
.

Definition build_return_wit_1 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (BuildPrefixState l heap_l i ) ” 
  &&  “ (PriorityQueuePrefix heap_l i ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((INT_MIN <= (Znth idx_2 heap_l 0)) /\ ((Znth idx_2 heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
|--
  EX (l_out: (@list Z)) ,
  “ (BuildPrefixState l l_out n_pre ) ” 
  &&  “ (PriorityQueuePrefix l_out n_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx l_out 0)) /\ ((Znth idx l_out 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre l_out )
.

Definition build_partial_solve_wit_1 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (BuildPrefixState l heap_l i ) ” 
  &&  “ (PriorityQueuePrefix heap_l i ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx heap_l 0)) /\ ((Znth idx heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (BuildPrefixState l heap_l i ) ” 
  &&  “ (PriorityQueuePrefix heap_l i ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx heap_l 0)) /\ ((Znth idx heap_l 0) <= INT_MAX))) ”
  &&  (((heap_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i heap_l 0))
  **  (IntArray.missing_i heap_pre i 0 n_pre heap_l )
.

Definition build_partial_solve_wit_2_pure := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (i: Z) (x: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (x = (Znth i heap_l 0)) ” 
  &&  “ (BuildPrefixState l heap_l i ) ” 
  &&  “ (PriorityQueuePrefix heap_l i ) ” 
  &&  “ (MaxHeapPrefix heap_l i ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((INT_MIN <= (Znth idx_2 heap_l 0)) /\ ((Znth idx_2 heap_l 0) <= INT_MAX))) ”
  &&  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.seg heap_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (heap_l)) )
  **  (IntArray.seg heap_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (heap_l)) )
|--
  “ (0 <= i) ” 
  &&  “ (i < 100000) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (i + 1 ))) -> ((INT_MIN <= (Znth idx (sublist (0) ((i + 1 )) (heap_l)) 0)) /\ ((Znth idx (sublist (0) ((i + 1 )) (heap_l)) 0) <= INT_MAX))) ” 
  &&  “ (((INT_MIN <= (Znth 0 (sublist (0) ((i + 1 )) (heap_l)) 0)) /\ ((Znth 0 (sublist (0) ((i + 1 )) (heap_l)) 0) <= INT_MAX)) /\ ((INT_MIN <= (Znth ((i + 1 ) - 1 ) (sublist (0) ((i + 1 )) (heap_l)) 0)) /\ ((Znth ((i + 1 ) - 1 ) (sublist (0) ((i + 1 )) (heap_l)) 0) <= INT_MAX))) ” 
  &&  “ (MaxHeapPrefix (sublist (0) ((i + 1 )) (heap_l)) i ) ” 
  &&  “ (x <= INT_MAX) ” 
  &&  “ (INT_MIN <= x) ” 
  &&  “ ((Znth i (sublist (0) ((i + 1 )) (heap_l)) 0) = x) ” 
  &&  “ ((Zlength ((sublist (0) ((i + 1 )) (heap_l)))) = (i + 1 )) ”
.

Definition build_partial_solve_wit_2_aux := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (i: Z) (x: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (x = (Znth i heap_l 0)) ” 
  &&  “ (BuildPrefixState l heap_l i ) ” 
  &&  “ (PriorityQueuePrefix heap_l i ) ” 
  &&  “ (MaxHeapPrefix heap_l i ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((INT_MIN <= (Znth idx_2 heap_l 0)) /\ ((Znth idx_2 heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (heap_l)) )
  **  (IntArray.seg heap_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (heap_l)) )
|--
  “ (0 <= i) ” 
  &&  “ (i < 100000) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (i + 1 ))) -> ((INT_MIN <= (Znth idx (sublist (0) ((i + 1 )) (heap_l)) 0)) /\ ((Znth idx (sublist (0) ((i + 1 )) (heap_l)) 0) <= INT_MAX))) ” 
  &&  “ (((INT_MIN <= (Znth 0 (sublist (0) ((i + 1 )) (heap_l)) 0)) /\ ((Znth 0 (sublist (0) ((i + 1 )) (heap_l)) 0) <= INT_MAX)) /\ ((INT_MIN <= (Znth ((i + 1 ) - 1 ) (sublist (0) ((i + 1 )) (heap_l)) 0)) /\ ((Znth ((i + 1 ) - 1 ) (sublist (0) ((i + 1 )) (heap_l)) 0) <= INT_MAX))) ” 
  &&  “ (MaxHeapPrefix (sublist (0) ((i + 1 )) (heap_l)) i ) ” 
  &&  “ (x <= INT_MAX) ” 
  &&  “ (INT_MIN <= x) ” 
  &&  “ ((Znth i (sublist (0) ((i + 1 )) (heap_l)) 0) = x) ” 
  &&  “ ((Zlength ((sublist (0) ((i + 1 )) (heap_l)))) = (i + 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (x = (Znth i heap_l 0)) ” 
  &&  “ (BuildPrefixState l heap_l i ) ” 
  &&  “ (PriorityQueuePrefix heap_l i ) ” 
  &&  “ (MaxHeapPrefix heap_l i ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((INT_MIN <= (Znth idx_2 heap_l 0)) /\ ((Znth idx_2 heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.seg heap_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (heap_l)) )
  **  (IntArray.seg heap_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (heap_l)) )
.

Definition build_partial_solve_wit_2 := build_partial_solve_wit_2_pure -> build_partial_solve_wit_2_aux.

(*----- Function pop -----*)

Definition pop_safety_wit_1 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PriorityQueuePrefix l n_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx l 0)) /\ ((Znth idx l 0) <= INT_MAX))) ”
  &&  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  (IntArray.full heap_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pop_safety_wit_2 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (ret: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PriorityQueuePrefix l n_pre ) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx l 0)) /\ ((Znth idx l 0) <= INT_MAX))) ”
  &&  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (IntArray.full heap_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_safety_wit_3 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (ret: Z) ,
  “ (n_pre <> 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PriorityQueuePrefix l n_pre ) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx l 0)) /\ ((Znth idx l 0) <= INT_MAX))) ”
  &&  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (IntArray.full heap_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pop_safety_wit_4 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (ret: Z) ,
  “ (n_pre <> 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PriorityQueuePrefix l n_pre ) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx l 0)) /\ ((Znth idx l 0) <= INT_MAX))) ”
  &&  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (IntArray.full heap_pre n_pre l )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition pop_safety_wit_5 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (ret: Z) ,
  “ (n_pre <> 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PriorityQueuePrefix l n_pre ) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx l 0)) /\ ((Znth idx l 0) <= INT_MAX))) ”
  &&  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (IntArray.full heap_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_safety_wit_6 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (ret: Z) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (PopLoopState l heap_l n_pre 0 ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx heap_l 0)) /\ ((Znth idx heap_l 0) <= INT_MAX))) ”
  &&  ((( &( "idx" ) )) # Int  |->_)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (IntArray.full heap_pre n_pre heap_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pop_safety_wit_7 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (idx: Z) (ret: Z) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (0 <= ((idx * 2 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre heap_l )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition pop_safety_wit_8 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (idx: Z) (ret: Z) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (0 <= ((idx * 2 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre heap_l )
|--
  “ (((idx * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((idx * 2 ) + 1 )) ”
.

Definition pop_safety_wit_9 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (idx: Z) (ret: Z) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (0 <= ((idx * 2 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre heap_l )
|--
  “ ((idx * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (idx * 2 )) ”
.

Definition pop_safety_wit_10 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (idx: Z) (ret: Z) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (0 <= ((idx * 2 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre heap_l )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition pop_safety_wit_11 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (idx: Z) (ret: Z) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (0 <= ((idx * 2 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre heap_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_safety_wit_12 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (idx: Z) (ret: Z) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (0 <= ((idx * 2 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre heap_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_safety_wit_13 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (idx: Z) (ret: Z) ,
  “ (((idx * 2 ) + 1 ) < (n_pre - 1 )) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (0 <= ((idx * 2 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre heap_l )
|--
  “ (((idx * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((idx * 2 ) + 1 )) ”
.

Definition pop_safety_wit_14 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (idx: Z) (ret: Z) ,
  “ (((idx * 2 ) + 1 ) < (n_pre - 1 )) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (0 <= ((idx * 2 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre heap_l )
|--
  “ ((idx * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (idx * 2 )) ”
.

Definition pop_safety_wit_15 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (idx: Z) (ret: Z) ,
  “ (((idx * 2 ) + 1 ) < (n_pre - 1 )) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (0 <= ((idx * 2 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre heap_l )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition pop_safety_wit_16 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (idx: Z) (ret: Z) ,
  “ (((idx * 2 ) + 1 ) < (n_pre - 1 )) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (0 <= ((idx * 2 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre heap_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_safety_wit_17 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (idx: Z) (ret: Z) ,
  “ (((idx * 2 ) + 1 ) < (n_pre - 1 )) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (0 <= ((idx * 2 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |-> ((idx * 2 ) + 1 ))
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre heap_l )
|--
  “ ((((idx * 2 ) + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((idx * 2 ) + 1 ) + 1 )) ”
.

Definition pop_safety_wit_18 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (idx: Z) (ret: Z) ,
  “ (((idx * 2 ) + 1 ) < (n_pre - 1 )) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (0 <= ((idx * 2 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |-> ((idx * 2 ) + 1 ))
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre heap_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_safety_wit_19 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (largest = left) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (n_pre - 1 )) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= (n_pre - 1 )) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  (IntArray.full heap_pre n_pre heap_l )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition pop_safety_wit_20 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (largest = left) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (n_pre - 1 )) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= (n_pre - 1 )) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "largest" ) )) # Int  |-> largest)
  **  (IntArray.full heap_pre n_pre heap_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_safety_wit_21 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (ret: Z) (idx: Z) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (PopReadyState l heap_l n_pre ret ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre heap_l )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition pop_safety_wit_22 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (ret: Z) (idx: Z) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (PopReadyState l heap_l n_pre ret ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre heap_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_entail_wit_1 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PriorityQueuePrefix l n_pre ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((INT_MIN <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Znth 0 l 0) = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) <= INT_MAX) ” 
  &&  “ (PriorityQueuePrefix l n_pre ) ” 
  &&  “ (PrefixMaxValue l n_pre (Znth 0 l 0) ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx l 0)) /\ ((Znth idx l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre l )
.

Definition pop_entail_wit_2 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (ret: Z) ,
  “ (n_pre = 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PriorityQueuePrefix l n_pre ) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((INT_MIN <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre l )
|--
  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (PopResult l l n_pre ret ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx l 0)) /\ ((Znth idx l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre l )
.

Definition pop_entail_wit_3 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (ret: Z) ,
  “ (n_pre <> 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PriorityQueuePrefix l n_pre ) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((INT_MIN <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre (replace_Znth (0) ((Znth (n_pre - 1 ) l 0)) (l)) )
|--
  EX (heap_l: (@list Z)) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (PopLoopState l heap_l n_pre 0 ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx heap_l 0)) /\ ((Znth idx heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
.

Definition pop_entail_wit_4 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l_2: (@list Z)) (ret: Z) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (PopLoopState l heap_l_2 n_pre 0 ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx heap_l_2 0)) /\ ((Znth idx heap_l_2 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l_2 )
|--
  EX (heap_l: (@list Z)) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < (n_pre - 1 )) ” 
  &&  “ (0 <= ((0 * 2 ) + 1 )) ” 
  &&  “ (((0 * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (PopLoopState l heap_l n_pre 0 ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
.

Definition pop_entail_wit_5 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l_2: (@list Z)) (idx: Z) (ret: Z) ,
  “ (((idx * 2 ) + 1 ) < (n_pre - 1 )) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (0 <= ((idx * 2 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (PopLoopState l heap_l_2 n_pre idx ) ” 
  &&  “ forall (pos_2: Z) , (((0 <= pos_2) /\ (pos_2 < n_pre)) -> ((INT_MIN <= (Znth pos_2 heap_l_2 0)) /\ ((Znth pos_2 heap_l_2 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l_2 )
|--
  EX (heap_l: (@list Z)) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) = ((idx * 2 ) + 1 )) ” 
  &&  “ ((((idx * 2 ) + 1 ) + 1 ) = (((idx * 2 ) + 1 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) = ((idx * 2 ) + 1 )) ” 
  &&  “ (0 <= ((idx * 2 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) < (n_pre - 1 )) ” 
  &&  “ (0 <= (((idx * 2 ) + 1 ) + 1 )) ” 
  &&  “ ((((idx * 2 ) + 1 ) + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
.

Definition pop_entail_wit_6_1 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l_2: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) ,
  “ ((Znth left heap_l_2 0) < (Znth right heap_l_2 0)) ” 
  &&  “ (right < (n_pre - 1 )) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (largest = left) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (n_pre - 1 )) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= (n_pre - 1 )) ” 
  &&  “ (PopLoopState l heap_l_2 n_pre idx ) ” 
  &&  “ forall (pos_2: Z) , (((0 <= pos_2) /\ (pos_2 < n_pre)) -> ((INT_MIN <= (Znth pos_2 heap_l_2 0)) /\ ((Znth pos_2 heap_l_2 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l_2 )
|--
  EX (heap_l: (@list Z)) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild heap_l (n_pre - 1 ) idx right ) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
.

Definition pop_entail_wit_6_2 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l_2: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) ,
  “ (right >= (n_pre - 1 )) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (largest = left) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (n_pre - 1 )) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= (n_pre - 1 )) ” 
  &&  “ (PopLoopState l heap_l_2 n_pre idx ) ” 
  &&  “ forall (pos_2: Z) , (((0 <= pos_2) /\ (pos_2 < n_pre)) -> ((INT_MIN <= (Znth pos_2 heap_l_2 0)) /\ ((Znth pos_2 heap_l_2 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l_2 )
|--
  EX (heap_l: (@list Z)) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild heap_l (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
.

Definition pop_entail_wit_6_3 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l_2: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) ,
  “ ((Znth left heap_l_2 0) >= (Znth right heap_l_2 0)) ” 
  &&  “ (right < (n_pre - 1 )) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (largest = left) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (n_pre - 1 )) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= (n_pre - 1 )) ” 
  &&  “ (PopLoopState l heap_l_2 n_pre idx ) ” 
  &&  “ forall (pos_2: Z) , (((0 <= pos_2) /\ (pos_2 < n_pre)) -> ((INT_MIN <= (Znth pos_2 heap_l_2 0)) /\ ((Znth pos_2 heap_l_2 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l_2 )
|--
  EX (heap_l: (@list Z)) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild heap_l (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
.

Definition pop_entail_wit_7 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l_2: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) ,
  “ ((Znth idx heap_l_2 0) >= (Znth largest heap_l_2 0)) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild heap_l_2 (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopLoopState l heap_l_2 n_pre idx ) ” 
  &&  “ forall (pos_2: Z) , (((0 <= pos_2) /\ (pos_2 < n_pre)) -> ((INT_MIN <= (Znth pos_2 heap_l_2 0)) /\ ((Znth pos_2 heap_l_2 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l_2 )
|--
  EX (heap_l: (@list Z)) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (n_pre - 1 )) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= (n_pre - 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ ((Znth idx heap_l 0) >= (Znth largest heap_l 0)) ” 
  &&  “ (PopSelectedChild heap_l (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopReadyState l heap_l n_pre ret ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
.

Definition pop_entail_wit_8 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) ,
  “ ((Znth idx heap_l 0) < (Znth largest heap_l 0)) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild heap_l (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos_2: Z) , (((0 <= pos_2) /\ (pos_2 < n_pre)) -> ((INT_MIN <= (Znth pos_2 heap_l 0)) /\ ((Znth pos_2 heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre (replace_Znth (largest) ((Znth idx heap_l 0)) ((replace_Znth (idx) ((Znth largest heap_l 0)) (heap_l)))) )
|--
  EX (heap_l_2: (@list Z)) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (n_pre - 1 )) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= (n_pre - 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (idx < largest) ” 
  &&  “ ((Znth idx heap_l 0) = (Znth largest heap_l_2 0)) ” 
  &&  “ (PopLoopState l heap_l_2 n_pre largest ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l_2 0)) /\ ((Znth pos heap_l_2 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l_2 )
.

Definition pop_entail_wit_9 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l_2: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) (tmp: Z) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (n_pre - 1 )) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= (n_pre - 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (idx < largest) ” 
  &&  “ (tmp = (Znth largest heap_l_2 0)) ” 
  &&  “ (PopLoopState l heap_l_2 n_pre largest ) ” 
  &&  “ forall (pos_2: Z) , (((0 <= pos_2) /\ (pos_2 < n_pre)) -> ((INT_MIN <= (Znth pos_2 heap_l_2 0)) /\ ((Znth pos_2 heap_l_2 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l_2 )
|--
  EX (heap_l: (@list Z)) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (0 <= ((largest * 2 ) + 1 )) ” 
  &&  “ (((largest * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (PopLoopState l heap_l n_pre largest ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
.

Definition pop_entail_wit_10_1 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l_2: (@list Z)) (idx: Z) (ret: Z) ,
  “ (((idx * 2 ) + 1 ) >= (n_pre - 1 )) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (0 <= ((idx * 2 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (PopLoopState l heap_l_2 n_pre idx ) ” 
  &&  “ forall (pos_2: Z) , (((0 <= pos_2) /\ (pos_2 < n_pre)) -> ((INT_MIN <= (Znth pos_2 heap_l_2 0)) /\ ((Znth pos_2 heap_l_2 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l_2 )
|--
  EX (heap_l: (@list Z)) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (PopReadyState l heap_l n_pre ret ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
.

Definition pop_entail_wit_10_2 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l_2: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (n_pre - 1 )) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= (n_pre - 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ ((Znth idx heap_l_2 0) >= (Znth largest heap_l_2 0)) ” 
  &&  “ (PopSelectedChild heap_l_2 (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopReadyState l heap_l_2 n_pre ret ) ” 
  &&  “ forall (pos_2: Z) , (((0 <= pos_2) /\ (pos_2 < n_pre)) -> ((INT_MIN <= (Znth pos_2 heap_l_2 0)) /\ ((Znth pos_2 heap_l_2 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l_2 )
|--
  EX (heap_l: (@list Z)) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (PopReadyState l heap_l n_pre ret ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
.

Definition pop_entail_wit_11 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (ret: Z) (idx: Z) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (PopReadyState l heap_l n_pre ret ) ” 
  &&  “ forall (pos_2: Z) , (((0 <= pos_2) /\ (pos_2 < n_pre)) -> ((INT_MIN <= (Znth pos_2 heap_l 0)) /\ ((Znth pos_2 heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre (replace_Znth ((n_pre - 1 )) (ret) (heap_l)) )
|--
  EX (l_out: (@list Z)) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (PopResult l l_out n_pre ret ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos l_out 0)) /\ ((Znth pos l_out 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre l_out )
.

Definition pop_return_wit_1 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (l_out_2: (@list Z)) (ret: Z) (idx_2: Z) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (0 <= idx_2) ” 
  &&  “ (idx_2 < (n_pre - 1 )) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (PopResult l l_out_2 n_pre ret ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos l_out_2 0)) /\ ((Znth pos l_out_2 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre l_out_2 )
|--
  EX (l_out: (@list Z)) ,
  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (PopResult l l_out n_pre ret ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx l_out 0)) /\ ((Znth idx l_out 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre l_out )
.

Definition pop_return_wit_2 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (ret: Z) ,
  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (PopResult l l n_pre ret ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((INT_MIN <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre l )
|--
  EX (l_out: (@list Z)) ,
  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (PopResult l l_out n_pre ret ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx l_out 0)) /\ ((Znth idx l_out 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre l_out )
.

Definition pop_partial_solve_wit_1 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PriorityQueuePrefix l n_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx l 0)) /\ ((Znth idx l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PriorityQueuePrefix l n_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx l 0)) /\ ((Znth idx l 0) <= INT_MAX))) ”
  &&  (((heap_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i heap_pre 0 0 n_pre l )
.

Definition pop_partial_solve_wit_2 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (ret: Z) ,
  “ (n_pre <> 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PriorityQueuePrefix l n_pre ) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx l 0)) /\ ((Znth idx l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre l )
|--
  “ (n_pre <> 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PriorityQueuePrefix l n_pre ) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx l 0)) /\ ((Znth idx l 0) <= INT_MAX))) ”
  &&  (((heap_pre + ((n_pre - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (n_pre - 1 ) l 0))
  **  (IntArray.missing_i heap_pre (n_pre - 1 ) 0 n_pre l )
.

Definition pop_partial_solve_wit_3 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (ret: Z) ,
  “ (n_pre <> 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PriorityQueuePrefix l n_pre ) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx l 0)) /\ ((Znth idx l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre l )
|--
  “ (n_pre <> 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PriorityQueuePrefix l n_pre ) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx l 0)) /\ ((Znth idx l 0) <= INT_MAX))) ”
  &&  (((heap_pre + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i heap_pre 0 0 n_pre l )
.

Definition pop_partial_solve_wit_4 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) ,
  “ (right < (n_pre - 1 )) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (largest = left) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (n_pre - 1 )) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= (n_pre - 1 )) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
|--
  “ (right < (n_pre - 1 )) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (largest = left) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (n_pre - 1 )) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= (n_pre - 1 )) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (((heap_pre + (left * sizeof(INT) ) )) # Int  |-> (Znth left heap_l 0))
  **  (IntArray.missing_i heap_pre left 0 n_pre heap_l )
.

Definition pop_partial_solve_wit_5 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) ,
  “ (right < (n_pre - 1 )) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (largest = left) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (n_pre - 1 )) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= (n_pre - 1 )) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
|--
  “ (right < (n_pre - 1 )) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (largest = left) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (n_pre - 1 )) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= (n_pre - 1 )) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (((heap_pre + (right * sizeof(INT) ) )) # Int  |-> (Znth right heap_l 0))
  **  (IntArray.missing_i heap_pre right 0 n_pre heap_l )
.

Definition pop_partial_solve_wit_6 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild heap_l (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
|--
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild heap_l (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (((heap_pre + (idx * sizeof(INT) ) )) # Int  |-> (Znth idx heap_l 0))
  **  (IntArray.missing_i heap_pre idx 0 n_pre heap_l )
.

Definition pop_partial_solve_wit_7 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild heap_l (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
|--
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild heap_l (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (((heap_pre + (largest * sizeof(INT) ) )) # Int  |-> (Znth largest heap_l 0))
  **  (IntArray.missing_i heap_pre largest 0 n_pre heap_l )
.

Definition pop_partial_solve_wit_8 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) ,
  “ ((Znth idx heap_l 0) < (Znth largest heap_l 0)) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild heap_l (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
|--
  “ ((Znth idx heap_l 0) < (Znth largest heap_l 0)) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild heap_l (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (((heap_pre + (idx * sizeof(INT) ) )) # Int  |-> (Znth idx heap_l 0))
  **  (IntArray.missing_i heap_pre idx 0 n_pre heap_l )
.

Definition pop_partial_solve_wit_9 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) ,
  “ ((Znth idx heap_l 0) < (Znth largest heap_l 0)) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild heap_l (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
|--
  “ ((Znth idx heap_l 0) < (Znth largest heap_l 0)) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild heap_l (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (((heap_pre + (largest * sizeof(INT) ) )) # Int  |-> (Znth largest heap_l 0))
  **  (IntArray.missing_i heap_pre largest 0 n_pre heap_l )
.

Definition pop_partial_solve_wit_10 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) ,
  “ ((Znth idx heap_l 0) < (Znth largest heap_l 0)) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild heap_l (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
|--
  “ ((Znth idx heap_l 0) < (Znth largest heap_l 0)) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild heap_l (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (((heap_pre + (idx * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i heap_pre idx 0 n_pre heap_l )
.

Definition pop_partial_solve_wit_11 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) ,
  “ ((Znth idx heap_l 0) < (Znth largest heap_l 0)) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild heap_l (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre (replace_Znth (idx) ((Znth largest heap_l 0)) (heap_l)) )
|--
  “ ((Znth idx heap_l 0) < (Znth largest heap_l 0)) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild heap_l (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopLoopState l heap_l n_pre idx ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (((heap_pre + (largest * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i heap_pre largest 0 n_pre (replace_Znth (idx) ((Znth largest heap_l 0)) (heap_l)) )
.

Definition pop_partial_solve_wit_12 := 
forall (n_pre: Z) (heap_pre: Z) (l: (@list Z)) (heap_l: (@list Z)) (ret: Z) (idx: Z) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (PopReadyState l heap_l n_pre ret ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (IntArray.full heap_pre n_pre heap_l )
|--
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (ret = (Znth 0 l 0)) ” 
  &&  “ (INT_MIN <= ret) ” 
  &&  “ (ret <= INT_MAX) ” 
  &&  “ (PrefixMaxValue l n_pre ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (PopReadyState l heap_l n_pre ret ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < n_pre)) -> ((INT_MIN <= (Znth pos heap_l 0)) /\ ((Znth pos heap_l 0) <= INT_MAX))) ”
  &&  (((heap_pre + ((n_pre - 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i heap_pre (n_pre - 1 ) 0 n_pre heap_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_push_safety_wit_1 : push_safety_wit_1.
Axiom proof_of_push_safety_wit_2 : push_safety_wit_2.
Axiom proof_of_push_safety_wit_3 : push_safety_wit_3.
Axiom proof_of_push_safety_wit_4 : push_safety_wit_4.
Axiom proof_of_push_safety_wit_5 : push_safety_wit_5.
Axiom proof_of_push_entail_wit_1 : push_entail_wit_1.
Axiom proof_of_push_entail_wit_2 : push_entail_wit_2.
Axiom proof_of_push_entail_wit_3 : push_entail_wit_3.
Axiom proof_of_push_entail_wit_4 : push_entail_wit_4.
Axiom proof_of_push_entail_wit_5 : push_entail_wit_5.
Axiom proof_of_push_entail_wit_6 : push_entail_wit_6.
Axiom proof_of_push_entail_wit_7_1 : push_entail_wit_7_1.
Axiom proof_of_push_entail_wit_7_2 : push_entail_wit_7_2.
Axiom proof_of_push_return_wit_1 : push_return_wit_1.
Axiom proof_of_push_partial_solve_wit_1 : push_partial_solve_wit_1.
Axiom proof_of_push_partial_solve_wit_2 : push_partial_solve_wit_2.
Axiom proof_of_push_partial_solve_wit_3 : push_partial_solve_wit_3.
Axiom proof_of_push_partial_solve_wit_4 : push_partial_solve_wit_4.
Axiom proof_of_push_partial_solve_wit_5 : push_partial_solve_wit_5.
Axiom proof_of_push_partial_solve_wit_6 : push_partial_solve_wit_6.
Axiom proof_of_push_partial_solve_wit_7 : push_partial_solve_wit_7.
Axiom proof_of_build_safety_wit_1 : build_safety_wit_1.
Axiom proof_of_build_safety_wit_2 : build_safety_wit_2.
Axiom proof_of_build_entail_wit_1 : build_entail_wit_1.
Axiom proof_of_build_entail_wit_2 : build_entail_wit_2.
Axiom proof_of_build_entail_wit_3 : build_entail_wit_3.
Axiom proof_of_build_entail_wit_4 : build_entail_wit_4.
Axiom proof_of_build_return_wit_1 : build_return_wit_1.
Axiom proof_of_build_partial_solve_wit_1 : build_partial_solve_wit_1.
Axiom proof_of_build_partial_solve_wit_2_pure : build_partial_solve_wit_2_pure.
Axiom proof_of_build_partial_solve_wit_2 : build_partial_solve_wit_2.
Axiom proof_of_pop_safety_wit_1 : pop_safety_wit_1.
Axiom proof_of_pop_safety_wit_2 : pop_safety_wit_2.
Axiom proof_of_pop_safety_wit_3 : pop_safety_wit_3.
Axiom proof_of_pop_safety_wit_4 : pop_safety_wit_4.
Axiom proof_of_pop_safety_wit_5 : pop_safety_wit_5.
Axiom proof_of_pop_safety_wit_6 : pop_safety_wit_6.
Axiom proof_of_pop_safety_wit_7 : pop_safety_wit_7.
Axiom proof_of_pop_safety_wit_8 : pop_safety_wit_8.
Axiom proof_of_pop_safety_wit_9 : pop_safety_wit_9.
Axiom proof_of_pop_safety_wit_10 : pop_safety_wit_10.
Axiom proof_of_pop_safety_wit_11 : pop_safety_wit_11.
Axiom proof_of_pop_safety_wit_12 : pop_safety_wit_12.
Axiom proof_of_pop_safety_wit_13 : pop_safety_wit_13.
Axiom proof_of_pop_safety_wit_14 : pop_safety_wit_14.
Axiom proof_of_pop_safety_wit_15 : pop_safety_wit_15.
Axiom proof_of_pop_safety_wit_16 : pop_safety_wit_16.
Axiom proof_of_pop_safety_wit_17 : pop_safety_wit_17.
Axiom proof_of_pop_safety_wit_18 : pop_safety_wit_18.
Axiom proof_of_pop_safety_wit_19 : pop_safety_wit_19.
Axiom proof_of_pop_safety_wit_20 : pop_safety_wit_20.
Axiom proof_of_pop_safety_wit_21 : pop_safety_wit_21.
Axiom proof_of_pop_safety_wit_22 : pop_safety_wit_22.
Axiom proof_of_pop_entail_wit_1 : pop_entail_wit_1.
Axiom proof_of_pop_entail_wit_2 : pop_entail_wit_2.
Axiom proof_of_pop_entail_wit_3 : pop_entail_wit_3.
Axiom proof_of_pop_entail_wit_4 : pop_entail_wit_4.
Axiom proof_of_pop_entail_wit_5 : pop_entail_wit_5.
Axiom proof_of_pop_entail_wit_6_1 : pop_entail_wit_6_1.
Axiom proof_of_pop_entail_wit_6_2 : pop_entail_wit_6_2.
Axiom proof_of_pop_entail_wit_6_3 : pop_entail_wit_6_3.
Axiom proof_of_pop_entail_wit_7 : pop_entail_wit_7.
Axiom proof_of_pop_entail_wit_8 : pop_entail_wit_8.
Axiom proof_of_pop_entail_wit_9 : pop_entail_wit_9.
Axiom proof_of_pop_entail_wit_10_1 : pop_entail_wit_10_1.
Axiom proof_of_pop_entail_wit_10_2 : pop_entail_wit_10_2.
Axiom proof_of_pop_entail_wit_11 : pop_entail_wit_11.
Axiom proof_of_pop_return_wit_1 : pop_return_wit_1.
Axiom proof_of_pop_return_wit_2 : pop_return_wit_2.
Axiom proof_of_pop_partial_solve_wit_1 : pop_partial_solve_wit_1.
Axiom proof_of_pop_partial_solve_wit_2 : pop_partial_solve_wit_2.
Axiom proof_of_pop_partial_solve_wit_3 : pop_partial_solve_wit_3.
Axiom proof_of_pop_partial_solve_wit_4 : pop_partial_solve_wit_4.
Axiom proof_of_pop_partial_solve_wit_5 : pop_partial_solve_wit_5.
Axiom proof_of_pop_partial_solve_wit_6 : pop_partial_solve_wit_6.
Axiom proof_of_pop_partial_solve_wit_7 : pop_partial_solve_wit_7.
Axiom proof_of_pop_partial_solve_wit_8 : pop_partial_solve_wit_8.
Axiom proof_of_pop_partial_solve_wit_9 : pop_partial_solve_wit_9.
Axiom proof_of_pop_partial_solve_wit_10 : pop_partial_solve_wit_10.
Axiom proof_of_pop_partial_solve_wit_11 : pop_partial_solve_wit_11.
Axiom proof_of_pop_partial_solve_wit_12 : pop_partial_solve_wit_12.

End VC_Correct.
