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
Require Import SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function build_prefix -----*)

Definition build_prefix_safety_wit_1 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_full pre_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_prefix_safety_wit_2 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_full pre_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_prefix_safety_wit_3 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (pref)) = 1) ” 
  &&  “ ((Znth 0 pref 0) = 0) ” 
  &&  “ (PrefixArrayPrefix l pref 0 ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 1 pref )
  **  (IntArray.undef_seg pre_pre 1 (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_prefix_safety_wit_4 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (PrefixArrayPrefix l pref i ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 (i + 1 ) pref )
  **  (IntArray.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition build_prefix_safety_wit_5 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (PrefixArrayPrefix l pref i ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 (i + 1 ) pref )
  **  (IntArray.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_prefix_safety_wit_6 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (PrefixArrayPrefix l pref i ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 (i + 1 ) pref )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) pref 0) + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (i - 0 ) pref 0) + (Znth i l 0) )) ”
.

Definition build_prefix_safety_wit_7 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (PrefixArrayPrefix l pref i ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pref) ((cons (((Znth (i - 0 ) pref 0) + (Znth i l 0) )) (nil)))) )
  **  (IntArray.undef_seg pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition build_prefix_entail_wit_1 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_2 ps 0)) /\ ((Znth idx_2 ps 0) <= INT_MAX))) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < n_pre)) -> (((-1000) <= (Znth idx_3 l 0)) /\ ((Znth idx_3 l 0) <= 1000))) ”
  &&  (((pre_pre + (0 * sizeof(INT) ) )) # Int  |-> 0)
  **  (IntArray.undef_seg pre_pre 1 (n_pre + 1 ) )
  **  (IntArray.full arr_pre n_pre l )
|--
  EX (pref: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (pref)) = 1) ” 
  &&  “ ((Znth 0 pref 0) = 0) ” 
  &&  “ (PrefixArrayPrefix l pref 0 ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 1 pref )
  **  (IntArray.undef_seg pre_pre 1 (n_pre + 1 ) )
.

Definition build_prefix_entail_wit_2 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref_2: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (pref_2)) = 1) ” 
  &&  “ ((Znth 0 pref_2 0) = 0) ” 
  &&  “ (PrefixArrayPrefix l pref_2 0 ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 1 pref_2 )
  **  (IntArray.undef_seg pre_pre 1 (n_pre + 1 ) )
|--
  EX (pref: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (PrefixArrayPrefix l pref 0 ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 (0 + 1 ) pref )
  **  (IntArray.undef_seg pre_pre (0 + 1 ) (n_pre + 1 ) )
.

Definition build_prefix_entail_wit_3 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref_2: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (PrefixArrayPrefix l pref_2 i ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pref_2) ((cons (((Znth (i - 0 ) pref_2 0) + (Znth i l 0) )) (nil)))) )
  **  (IntArray.undef_seg pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (IntArray.full arr_pre n_pre l )
|--
  EX (pref: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (PrefixArrayPrefix l pref (i + 1 ) ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 ((i + 1 ) + 1 ) pref )
  **  (IntArray.undef_seg pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
.

Definition build_prefix_return_wit_1 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref: (@list Z)) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (PrefixArrayPrefix l pref i ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 (i + 1 ) pref )
  **  (IntArray.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  EX (ps: (@list Z)) ,
  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full pre_pre (n_pre + 1 ) ps )
.

Definition build_prefix_partial_solve_wit_1 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_full pre_pre (n_pre + 1 ) )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (((pre_pre + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg pre_pre 1 (n_pre + 1 ) )
  **  (IntArray.full arr_pre n_pre l )
.

Definition build_prefix_partial_solve_wit_2 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (PrefixArrayPrefix l pref i ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 (i + 1 ) pref )
  **  (IntArray.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (PrefixArrayPrefix l pref i ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (((pre_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth (i - 0 ) pref 0))
  **  (IntArray.missing_i pre_pre i 0 (i + 1 ) pref )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
.

Definition build_prefix_partial_solve_wit_3 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (PrefixArrayPrefix l pref i ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.seg pre_pre 0 (i + 1 ) pref )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (PrefixArrayPrefix l pref i ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (((arr_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i arr_pre i 0 n_pre l )
  **  (IntArray.seg pre_pre 0 (i + 1 ) pref )
  **  (IntArray.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
.

Definition build_prefix_partial_solve_wit_4 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (PrefixArrayPrefix l pref i ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 (i + 1 ) pref )
  **  (IntArray.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (PrefixArrayPrefix l pref i ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (((pre_pre + ((i + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 (i + 1 ) pref )
.

(*----- Function superPiano -----*)

Definition superPiano_safety_wit_1 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((-9223372036854775808) <= ans) ” 
  &&  “ (ans <= 9223372036854775807) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  ((( &( "heap_cap" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_full prefix_pre (n_pre + 1 ) )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_start_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_lo_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_hi_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_best_pre ((n_pre + k_pre ) + 1 ) )
|--
  “ (((n_pre + k_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n_pre + k_pre ) + 1 )) ”
.

Definition superPiano_safety_wit_2 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((-9223372036854775808) <= ans) ” 
  &&  “ (ans <= 9223372036854775807) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  ((( &( "heap_cap" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_full prefix_pre (n_pre + 1 ) )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_start_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_lo_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_hi_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_best_pre ((n_pre + k_pre ) + 1 ) )
|--
  “ ((n_pre + k_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + k_pre )) ”
.

Definition superPiano_safety_wit_3 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((-9223372036854775808) <= ans) ” 
  &&  “ (ans <= 9223372036854775807) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  ((( &( "heap_cap" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_full prefix_pre (n_pre + 1 ) )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_start_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_lo_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_hi_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_best_pre ((n_pre + k_pre ) + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_4 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (heap_cap: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ ((Zlength (st_slots)) = ((n_pre + 1 ) * ST_LEVELS )) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition superPiano_safety_wit_5 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (heap_cap: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ ((Zlength (st_slots)) = ((n_pre + 1 ) * ST_LEVELS )) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_6 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (heap_cap: Z) (hsize: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ (hsize = ((n_pre - L_pre ) + 1 )) ” 
  &&  “ ((hsize + k_pre ) < heap_cap) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (InitialFrontierState ps n_pre L_pre R_pre (sublist (0) (hsize) (slots)) ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition superPiano_safety_wit_7 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (heap_cap: Z) (hsize: Z) (total: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ (hsize = ((n_pre - L_pre ) + 1 )) ” 
  &&  “ ((hsize + k_pre ) < heap_cap) ” 
  &&  “ (total = 0) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre nil 0 0 (sublist (0) (hsize) (slots)) ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  ((( &( "t" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition superPiano_safety_wit_8 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ ((hsize - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (hsize - 1 )) ”
.

Definition superPiano_safety_wit_9 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_10 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ ((total + value ) <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= (total + value )) ”
.

Definition superPiano_safety_wit_11 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "has_left" ) )) # Int  |->_)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition superPiano_safety_wit_12 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "left_best" ) )) # Int  |->_)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition superPiano_safety_wit_13 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "left_value" ) )) # Int  |->_)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition superPiano_safety_wit_14 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "has_right" ) )) # Int  |->_)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition superPiano_safety_wit_15 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "right_best" ) )) # Int  |->_)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition superPiano_safety_wit_16 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "right_value" ) )) # Int  |->_)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition superPiano_safety_wit_17 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ ((best - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (best - 1 )) ”
.

Definition superPiano_safety_wit_18 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_19 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ ((best - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (best - 1 )) ”
.

Definition superPiano_safety_wit_20 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition superPiano_safety_wit_21 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_22 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_23 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (((Znth retval ps 0) - (Znth (start - 1 ) ps 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth retval ps 0) - (Znth (start - 1 ) ps 0) )) ”
.

Definition superPiano_safety_wit_24 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((start - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (start - 1 )) ”
.

Definition superPiano_safety_wit_25 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_26 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval ps 0) - (Znth (start - 1 ) ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_27 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval ps 0) - (Znth (start - 1 ) ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((best + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (best + 1 )) ”
.

Definition superPiano_safety_wit_28 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ ((best + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (best + 1 )) ”
.

Definition superPiano_safety_wit_29 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_30 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval ps 0) - (Znth (start - 1 ) ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_31 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ ((best + 1 ) <= hi) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval ps 0) - (Znth (start - 1 ) ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((best + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (best + 1 )) ”
.

Definition superPiano_safety_wit_32 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ ((best + 1 ) <= hi) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval ps 0) - (Znth (start - 1 ) ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition superPiano_safety_wit_33 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ ((best + 1 ) <= hi) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval ps 0) - (Znth (start - 1 ) ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_34 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ ((best + 1 ) <= hi) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval ps 0) - (Znth (start - 1 ) ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_35 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ ((best + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (best + 1 )) ”
.

Definition superPiano_safety_wit_36 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition superPiano_safety_wit_37 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_38 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_39 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ (RangeArgmax ps (best + 1 ) hi retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval) ” 
  &&  “ (retval <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> retval)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (((Znth retval ps 0) - (Znth (start - 1 ) ps 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth retval ps 0) - (Znth (start - 1 ) ps 0) )) ”
.

Definition superPiano_safety_wit_40 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ (RangeArgmax ps (best + 1 ) hi retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval) ” 
  &&  “ (retval <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> retval)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((start - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (start - 1 )) ”
.

Definition superPiano_safety_wit_41 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ (RangeArgmax ps (best + 1 ) hi retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval) ” 
  &&  “ (retval <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> retval)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_42 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval_2: Z) (retval: Z) ,
  “ (RangeArgmax ps (best + 1 ) hi retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval) ” 
  &&  “ (retval <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) retval_2 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < (n_pre + 1 )) ” 
  &&  “ (lo <= retval_2) ” 
  &&  “ (retval_2 <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> retval)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval_2 ps 0) - (Znth (start - 1 ) ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval_2)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (((Znth retval ps 0) - (Znth (start - 1 ) ps 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth retval ps 0) - (Znth (start - 1 ) ps 0) )) ”
.

Definition superPiano_safety_wit_43 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) (retval_2: Z) ,
  “ (RangeArgmax ps (best + 1 ) hi retval_2 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval_2) ” 
  &&  “ (retval_2 <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> retval_2)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval ps 0) - (Znth (start - 1 ) ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((start - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (start - 1 )) ”
.

Definition superPiano_safety_wit_44 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) (retval_2: Z) ,
  “ (RangeArgmax ps (best + 1 ) hi retval_2 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval_2) ” 
  &&  “ (retval_2 <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> retval_2)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval ps 0) - (Znth (start - 1 ) ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_45 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) (retval_2: Z) ,
  “ (RangeArgmax ps (best + 1 ) hi retval_2 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval_2) ” 
  &&  “ (retval_2 <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> ((Znth retval_2 ps 0) - (Znth (start - 1 ) ps 0) ))
  **  ((( &( "right_best" ) )) # Int  |-> retval_2)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval ps 0) - (Znth (start - 1 ) ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_46 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ (RangeArgmax ps (best + 1 ) hi retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval) ” 
  &&  “ (retval <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> ((Znth retval ps 0) - (Znth (start - 1 ) ps 0) ))
  **  ((( &( "right_best" ) )) # Int  |-> retval)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_47 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (left_best: Z) (best: Z) (lo: Z) (start: Z) (left_value: Z) (total: Z) (hi: Z) (right_best: Z) (right_value: Z) (value: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) (nil)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (hi <= best) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ ((best - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (best - 1 )) ”
.

Definition superPiano_safety_wit_48 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (left_best: Z) (best: Z) (lo: Z) (start: Z) (left_value: Z) (total: Z) (hi: Z) (right_best: Z) (right_value: Z) (value: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) (nil)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (hi <= best) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_49 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)))) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ ((best - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (best - 1 )) ”
.

Definition superPiano_safety_wit_50 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)))) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_51 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots hsize left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)))) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ ((hsize + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (hsize + 1 )) ”
.

Definition superPiano_safety_wit_52 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots hsize left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)))) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_53 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (left_best: Z) (best: Z) (lo: Z) (start: Z) (left_value: Z) (total: Z) (hi: Z) (right_best: Z) (right_value: Z) (value: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots hsize left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) (nil)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (hi <= best) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ ((hsize + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (hsize + 1 )) ”
.

Definition superPiano_safety_wit_54 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (left_best: Z) (best: Z) (lo: Z) (start: Z) (left_value: Z) (total: Z) (hi: Z) (right_best: Z) (right_value: Z) (value: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots hsize left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) (nil)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (hi <= best) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_55 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (left_best: Z) (best: Z) (lo: Z) (start: Z) (left_value: Z) (total: Z) (hi: Z) (right_best: Z) (right_value: Z) (value: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (has_left = 0) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots hsize left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) (nil)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (hi <= best) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize + 1 ))
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ False ”
.

Definition superPiano_safety_wit_56 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (has_left = 0) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots hsize left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)))) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize + 1 ))
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ False ”
.

Definition superPiano_safety_wit_57 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (has_left <> 0) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots hsize left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)))) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ” 
  &&  “ (has_right = 0) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize + 1 ))
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ False ”
.

Definition superPiano_safety_wit_58 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (left_best: Z) (left_value: Z) (right_best: Z) (right_value: Z) (t: Z) (hsize: Z) (total: Z) (best: Z) (start: Z) (lo: Z) (hi: Z) (value: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 0) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (left_best = 0) ” 
  &&  “ (left_value = 0) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((hsize + (k_pre - (t + 1 ) ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total nil (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (lo = best) ” 
  &&  “ (best = hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ” 
  &&  “ (has_right <> 0) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ False ”
.

Definition superPiano_safety_wit_59 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (left_best: Z) (best: Z) (lo: Z) (start: Z) (left_value: Z) (total: Z) (hi: Z) (right_best: Z) (right_value: Z) (value: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (has_left <> 0) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots hsize left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) (nil)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (hi <= best) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ” 
  &&  “ (has_right <> 0) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize + 1 ))
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ False ”
.

Definition superPiano_safety_wit_60 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (has_left <> 0) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots hsize left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)))) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ” 
  &&  “ (has_right <> 0) ” 
  &&  “ (has_left = 0) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize + 1 ))
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ False ”
.

Definition superPiano_safety_wit_61 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (left_best: Z) (left_value: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (value: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 0) ” 
  &&  “ (left_best = 0) ” 
  &&  “ (left_value = 0) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ ((best + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (best + 1 )) ”
.

Definition superPiano_safety_wit_62 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (left_best: Z) (left_value: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (value: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 0) ” 
  &&  “ (left_best = 0) ” 
  &&  “ (left_value = 0) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_63 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (left_best: Z) (left_value: Z) (value: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ ((best + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (best + 1 )) ”
.

Definition superPiano_safety_wit_64 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (left_best: Z) (left_value: Z) (value: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_65 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (left_best: Z) (left_value: Z) (value: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots hsize right_value start (best + 1 ) hi right_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ ((hsize + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (hsize + 1 )) ”
.

Definition superPiano_safety_wit_66 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (left_best: Z) (left_value: Z) (value: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots hsize right_value start (best + 1 ) hi right_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_67 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (left_best: Z) (left_value: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (value: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots hsize right_value start (best + 1 ) hi right_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 0) ” 
  &&  “ (left_best = 0) ” 
  &&  “ (left_value = 0) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ ((hsize + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (hsize + 1 )) ”
.

Definition superPiano_safety_wit_68 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (left_best: Z) (left_value: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (value: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots hsize right_value start (best + 1 ) hi right_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 0) ” 
  &&  “ (left_best = 0) ” 
  &&  “ (left_value = 0) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_69 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (left_best: Z) (right_best: Z) (left_value: Z) (right_value: Z) (t: Z) (hsize: Z) (total: Z) (best: Z) (start: Z) (hi: Z) (lo: Z) (value: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= has_left) ” 
  &&  “ (has_left <= 1) ” 
  &&  “ (0 <= has_right) ” 
  &&  “ (has_right <= 1) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ (INT_MIN <= left_value) ” 
  &&  “ (left_value <= INT_MAX) ” 
  &&  “ (INT_MIN <= right_value) ” 
  &&  “ (right_value <= INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((hsize + (k_pre - (t + 1 ) ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ ((t + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (t + 1 )) ”
.

Definition superPiano_entail_wit_1 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (ps_3: (@list Z)) ,
  “ (PrefixSums l ps_3 ) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_3 ps_3 0)) /\ ((Znth idx_3 ps_3 0) <= INT_MAX))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_4 ps_2 0)) /\ ((Znth idx_4 ps_2 0) <= INT_MAX))) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((-9223372036854775808) <= ans_2) ” 
  &&  “ (ans_2 <= 9223372036854775807) ” 
  &&  “ forall (idx_5: Z) , (((0 <= idx_5) /\ (idx_5 < n_pre)) -> (((-1000) <= (Znth idx_5 l 0)) /\ ((Znth idx_5 l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_3 )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_start_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_lo_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_hi_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_best_pre ((n_pre + k_pre ) + 1 ) )
|--
  EX (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ ((Zlength (st_slots)) = ((n_pre + 1 ) * ST_LEVELS )) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_start_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_lo_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_hi_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_best_pre ((n_pre + k_pre ) + 1 ) )
.

Definition superPiano_entail_wit_2 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (heap_cap: Z) (st_out: (@list Z)) ,
  “ (SparseArgmaxBuilt ps_2 st_out (n_pre + 1 ) ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ ((Zlength (st_slots_2)) = ((n_pre + 1 ) * ST_LEVELS )) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_3 ps_2 0)) /\ ((Znth idx_3 ps_2 0) <= INT_MAX))) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l 0)) /\ ((Znth idx_4 l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_out )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
|--
  EX (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
.

Definition superPiano_entail_wit_3 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (heap_cap: Z) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ (retval = ((n_pre - L_pre ) + 1 )) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (NodeHeapState slots_2 retval ) ” 
  &&  “ (InitialFrontierState ps_2 n_pre L_pre R_pre (sublist (0) (retval) (slots_2)) ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_3 ps_2 0)) /\ ((Znth idx_3 ps_2 0) <= INT_MAX))) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l 0)) /\ ((Znth idx_4 l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
  **  (IntArray.full heap_value_pre heap_cap vals_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_2 )
  **  (IntArray.full arr_pre n_pre l )
|--
  EX (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ (retval = ((n_pre - L_pre ) + 1 )) ” 
  &&  “ ((retval + k_pre ) < heap_cap) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots retval ) ” 
  &&  “ (InitialFrontierState ps n_pre L_pre R_pre (sublist (0) (retval) (slots)) ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
.

Definition superPiano_entail_wit_4 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (heap_cap: Z) (hsize: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ (hsize = ((n_pre - L_pre ) + 1 )) ” 
  &&  “ ((hsize + k_pre ) < heap_cap) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_3 ps_2 0)) /\ ((Znth idx_3 ps_2 0) <= INT_MAX))) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (NodeHeapState slots_2 hsize ) ” 
  &&  “ (InitialFrontierState ps_2 n_pre L_pre R_pre (sublist (0) (hsize) (slots_2)) ) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l 0)) /\ ((Znth idx_4 l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
  **  (IntArray.full heap_value_pre heap_cap vals_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_2 )
|--
  EX (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ (hsize = ((n_pre - L_pre ) + 1 )) ” 
  &&  “ ((hsize + k_pre ) < heap_cap) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre nil 0 0 (sublist (0) (hsize) (slots)) ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
.

Definition superPiano_entail_wit_5 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (heap_cap: Z) (hsize: Z) (total: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ (hsize = ((n_pre - L_pre ) + 1 )) ” 
  &&  “ ((hsize + k_pre ) < heap_cap) ” 
  &&  “ (total = 0) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_2 ps_2 0)) /\ ((Znth idx_2 ps_2 0) <= INT_MAX))) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (NodeHeapState slots_2 hsize ) ” 
  &&  “ (FrontierState ps_2 n_pre L_pre R_pre nil 0 0 (sublist (0) (hsize) (slots_2)) ) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < n_pre)) -> (((-1000) <= (Znth idx_3 l 0)) /\ ((Znth idx_3 l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
  **  (IntArray.full heap_value_pre heap_cap vals_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_2 )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - 0 ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen 0 total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ ((0 < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
.

Definition superPiano_entail_wit_6 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (chosen_2: (@list Z)) (total: Z) (hsize: Z) (t: Z) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (ans_2: Z) (st_slots_2: (@list Z)) (ps_2: (@list Z)) (heap_cap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) ,
  “ (retval_5 = (heap_top_best (slots_2))) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (NodeHeapState slots_2 hsize ) ” 
  &&  “ (retval_4 = (heap_top_hi (slots_2))) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (NodeHeapState slots_2 hsize ) ” 
  &&  “ (retval_3 = (heap_top_lo (slots_2))) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (NodeHeapState slots_2 hsize ) ” 
  &&  “ (retval_2 = (heap_top_start (slots_2))) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (NodeHeapState slots_2 hsize ) ” 
  &&  “ (retval = (heap_top_value (slots_2))) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (NodeHeapState slots_2 hsize ) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps_2 n_pre L_pre R_pre chosen_2 t total (sublist (0) (hsize) (slots_2)) ) ” 
  &&  “ (NodeHeapState slots_2 hsize ) ” 
  &&  “ ((t < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_2 )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (retval = (heap_top_value (slots))) ” 
  &&  “ (retval_2 = (heap_top_start (slots))) ” 
  &&  “ (retval_3 = (heap_top_lo (slots))) ” 
  &&  “ (retval_4 = (heap_top_hi (slots))) ” 
  &&  “ (retval_5 = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre retval retval_2 retval_3 retval_4 retval_5 ) ” 
  &&  “ (1 <= retval_2) ” 
  &&  “ (retval_2 <= n_pre) ” 
  &&  “ (0 <= (retval_2 - 1 )) ” 
  &&  “ ((retval_2 - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((retval_2 + L_pre ) - 1 ) <= retval_3) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= retval_5) ” 
  &&  “ (retval_5 <= retval_4) ” 
  &&  “ (retval_4 <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
.

Definition superPiano_entail_wit_7 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) (retval_2: Z) ,
  “ (RangeArgmax ps (best + 1 ) hi retval_2 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval_2) ” 
  &&  “ (retval_2 <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots_2 hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots_2))) ” 
  &&  “ (start = (heap_top_start (slots_2))) ” 
  &&  “ (lo = (heap_top_lo (slots_2))) ” 
  &&  “ (hi = (heap_top_hi (slots_2))) ” 
  &&  “ (best = (heap_top_best (slots_2))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen_2 t total (sublist (0) (hsize) (slots_2)) ) ” 
  &&  “ (NodeHeapState slots_2 hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps_2: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (1 = 1) ” 
  &&  “ (1 = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= (hsize - 1 )) ” 
  &&  “ ((hsize - 1 ) < heap_cap) ” 
  &&  “ ((((hsize - 1 ) + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps_2 n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) (total + value ) (cons ((mkNode (((Znth retval ps 0) - (Znth (start - 1 ) ps 0) )) (start) (lo) ((best - 1 )) (retval))) ((cons ((mkNode (((Znth retval_2 ps 0) - (Znth (start - 1 ) ps 0) )) (start) ((best + 1 )) (hi) (retval_2))) (nil)))) (sublist (0) ((hsize - 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize - 1 ) ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps_2 lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre ((Znth retval ps 0) - (Znth (start - 1 ) ps 0) ) start lo (best - 1 ) retval ) ” 
  &&  “ (RangeArgmax ps_2 (best + 1 ) hi retval_2 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval_2) ” 
  &&  “ (retval_2 <= hi) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre ((Znth retval_2 ps 0) - (Znth (start - 1 ) ps 0) ) start (best + 1 ) hi retval_2 ) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
.

Definition superPiano_entail_wit_8 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ ((best + 1 ) > hi) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots_2 hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots_2))) ” 
  &&  “ (start = (heap_top_start (slots_2))) ” 
  &&  “ (lo = (heap_top_lo (slots_2))) ” 
  &&  “ (hi = (heap_top_hi (slots_2))) ” 
  &&  “ (best = (heap_top_best (slots_2))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen_2 t total (sublist (0) (hsize) (slots_2)) ) ” 
  &&  “ (NodeHeapState slots_2 hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps_2: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (1 = 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= (hsize - 1 )) ” 
  &&  “ ((hsize - 1 ) < heap_cap) ” 
  &&  “ ((((hsize - 1 ) + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps_2 n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) (total + value ) (cons ((mkNode (((Znth retval ps 0) - (Znth (start - 1 ) ps 0) )) (start) (lo) ((best - 1 )) (retval))) (nil)) (sublist (0) ((hsize - 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize - 1 ) ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps_2 lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre ((Znth retval ps 0) - (Znth (start - 1 ) ps 0) ) start lo (best - 1 ) retval ) ” 
  &&  “ (hi <= best) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
.

Definition superPiano_entail_wit_9 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((best + 1 ) > hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots_2 hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots_2))) ” 
  &&  “ (start = (heap_top_start (slots_2))) ” 
  &&  “ (lo = (heap_top_lo (slots_2))) ” 
  &&  “ (hi = (heap_top_hi (slots_2))) ” 
  &&  “ (best = (heap_top_best (slots_2))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps_2 n_pre L_pre R_pre chosen_2 t total (sublist (0) (hsize) (slots_2)) ) ” 
  &&  “ (NodeHeapState slots_2 hsize ) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= (hsize - 1 )) ” 
  &&  “ ((hsize - 1 ) < heap_cap) ” 
  &&  “ (((hsize - 1 ) + (k_pre - (t + 1 ) ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) (total + value ) nil (sublist (0) ((hsize - 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize - 1 ) ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (lo = best) ” 
  &&  “ (best = hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
.

Definition superPiano_entail_wit_10_1 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (left_best: Z) (left_value: Z) (right_best: Z) (right_value: Z) (t: Z) (hsize: Z) (total: Z) (best: Z) (start: Z) (lo: Z) (hi: Z) (value: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 0) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (left_best = 0) ” 
  &&  “ (left_value = 0) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((hsize + (k_pre - (t + 1 ) ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total nil (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (lo = best) ” 
  &&  “ (best = hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ” 
  &&  “ (has_right = 0) ”
  &&  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 0) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (left_best = 0) ” 
  &&  “ (left_value = 0) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((hsize + (k_pre - (t + 1 ) ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total nil (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (lo = best) ” 
  &&  “ (best = hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ” 
  &&  “ (has_right = 0) ”
  &&  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests ))
  ||
  (EX (vals_out: (@list Z))  (starts_out: (@list Z))  (los_out: (@list Z))  (his_out: (@list Z))  (bests_out: (@list Z))  (slots_out: (@list ((((Z * Z) * Z) * Z) * Z)))  (chosen_2: (@list Z))  (hsize_2: Z)  (vals_2: (@list Z))  (starts_2: (@list Z))  (los_2: (@list Z))  (his_2: (@list Z))  (bests_2: (@list Z))  (slots_2: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans_2: Z)  (st_slots_2: (@list Z))  (ps_2: (@list Z)) ,
  “ (has_left <> 0) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize_2 + 1 ) ) ” 
  &&  “ (FrontierPushFields slots_2 hsize_2 left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize_2) ” 
  &&  “ (hsize_2 < heap_cap) ” 
  &&  “ (((hsize_2 + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps_2 n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) (nil)) (sublist (0) (hsize_2) (slots_2)) ) ” 
  &&  “ (NodeHeapState slots_2 hsize_2 ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps_2 lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (hi <= best) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ” 
  &&  “ (has_right = 0) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "hsize" ) )) # Int  |-> (hsize_2 + 1 ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 ))
.

Definition superPiano_entail_wit_10_2 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_3: (@list Z)) (ans_3: Z) (st_slots_3: (@list Z)) (slots_3: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_3: (@list Z)) (starts_3: (@list Z)) (los_3: (@list Z)) (his_3: (@list Z)) (bests_3: (@list Z)) (chosen_3: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize_3: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) (vals_out_2: (@list Z)) (starts_out_2: (@list Z)) (los_out_2: (@list Z)) (his_out_2: (@list Z)) (bests_out_2: (@list Z)) (slots_out_2: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (has_left <> 0) ” 
  &&  “ ((Zlength (slots_out_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out_2 vals_out_2 starts_out_2 los_out_2 his_out_2 bests_out_2 ) ” 
  &&  “ (NodeHeapState slots_out_2 (hsize_3 + 1 ) ) ” 
  &&  “ (FrontierPushFields slots_3 hsize_3 left_value start lo (best - 1 ) left_best slots_out_2 ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_3 ) ” 
  &&  “ (SparseArgmaxBuilt ps_3 st_slots_3 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_3 n_pre L_pre R_pre k_pre ans_3 ) ” 
  &&  “ ((Zlength (slots_3)) = heap_cap) ” 
  &&  “ (NodeArrays slots_3 vals_3 starts_3 los_3 his_3 bests_3 ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize_3) ” 
  &&  “ (hsize_3 < heap_cap) ” 
  &&  “ (((hsize_3 + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps_3 n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_3)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)))) (sublist (0) (hsize_3) (slots_3)) ) ” 
  &&  “ (NodeHeapState slots_3 hsize_3 ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps_3 lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps_3 n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (RangeArgmax ps_3 (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps_3 n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps_3 n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < n_pre)) -> (((-1000) <= (Znth idx_3 l 0)) /\ ((Znth idx_3 l 0) <= 1000))) ” 
  &&  “ (has_right = 0) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_out_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_out_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_out_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_out_2 )
  **  ((( &( "hsize" ) )) # Int  |-> (hsize_3 + 1 ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_3 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_3 )
|--
  (EX (chosen: (@list Z))  (hsize: Z)  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 0) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (left_best = 0) ” 
  &&  “ (left_value = 0) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((hsize + (k_pre - (t + 1 ) ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total nil (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (lo = best) ” 
  &&  “ (best = hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ” 
  &&  “ (has_right = 0) ”
  &&  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests ))
  ||
  (EX (vals_out: (@list Z))  (starts_out: (@list Z))  (los_out: (@list Z))  (his_out: (@list Z))  (bests_out: (@list Z))  (slots_out: (@list ((((Z * Z) * Z) * Z) * Z)))  (chosen_2: (@list Z))  (hsize_2: Z)  (vals_2: (@list Z))  (starts_2: (@list Z))  (los_2: (@list Z))  (his_2: (@list Z))  (bests_2: (@list Z))  (slots_2: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans_2: Z)  (st_slots_2: (@list Z))  (ps_2: (@list Z)) ,
  “ (has_left <> 0) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize_2 + 1 ) ) ” 
  &&  “ (FrontierPushFields slots_2 hsize_2 left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize_2) ” 
  &&  “ (hsize_2 < heap_cap) ” 
  &&  “ (((hsize_2 + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps_2 n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) (nil)) (sublist (0) (hsize_2) (slots_2)) ) ” 
  &&  “ (NodeHeapState slots_2 hsize_2 ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps_2 lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (hi <= best) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ” 
  &&  “ (has_right = 0) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "hsize" ) )) # Int  |-> (hsize_2 + 1 ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 ))
.

Definition superPiano_entail_wit_10_3 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (left_best: Z) (best: Z) (lo: Z) (start: Z) (left_value: Z) (total: Z) (hi: Z) (right_best: Z) (right_value: Z) (value: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (has_left <> 0) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots_2 hsize left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps_2 n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) (nil)) (sublist (0) (hsize) (slots_2)) ) ” 
  &&  “ (NodeHeapState slots_2 hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps_2 lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (hi <= best) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ” 
  &&  “ (has_right = 0) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
|--
  (EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 0) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (left_best = 0) ” 
  &&  “ (left_value = 0) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= (hsize + 1 )) ” 
  &&  “ ((hsize + 1 ) < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - (t + 1 ) ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total nil (sublist (0) ((hsize + 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize + 1 ) ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (lo = best) ” 
  &&  “ (best = hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ” 
  &&  “ (has_right = 0) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests ))
  ||
  (“ (has_left <> 0) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots_2 hsize left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps_2 n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) (nil)) (sublist (0) (hsize) (slots_2)) ) ” 
  &&  “ (NodeHeapState slots_2 hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps_2 lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (hi <= best) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ” 
  &&  “ (has_right = 0) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 ))
.

Definition superPiano_entail_wit_11_1 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_3: (@list Z)) (ans_3: Z) (st_slots_3: (@list Z)) (slots_3: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_3: (@list Z)) (starts_3: (@list Z)) (los_3: (@list Z)) (his_3: (@list Z)) (bests_3: (@list Z)) (chosen_3: (@list Z)) (heap_cap: Z) (has_left_2: Z) (has_right_2: Z) (left_best_2: Z) (left_value_2: Z) (right_best: Z) (right_value_2: Z) (t: Z) (hsize_3: Z) (total_3: Z) (best: Z) (start: Z) (lo: Z) (hi: Z) (value: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_3 ) ” 
  &&  “ (SparseArgmaxBuilt ps_3 st_slots_3 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_3 n_pre L_pre R_pre k_pre ans_3 ) ” 
  &&  “ ((Zlength (slots_3)) = heap_cap) ” 
  &&  “ (NodeArrays slots_3 vals_3 starts_3 los_3 his_3 bests_3 ) ” 
  &&  “ (has_left_2 = 0) ” 
  &&  “ (has_right_2 = 0) ” 
  &&  “ (left_best_2 = 0) ” 
  &&  “ (left_value_2 = 0) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value_2 = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize_3) ” 
  &&  “ (hsize_3 < heap_cap) ” 
  &&  “ ((hsize_3 + (k_pre - (t + 1 ) ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps_3 n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_3)) (t + 1 ) total_3 nil (sublist (0) (hsize_3) (slots_3)) ) ” 
  &&  “ (NodeHeapState slots_3 hsize_3 ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (lo = best) ” 
  &&  “ (best = hi) ” 
  &&  “ (ValidNodeFields ps_3 n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < n_pre)) -> (((-1000) <= (Znth idx_3 l 0)) /\ ((Znth idx_3 l 0) <= 1000))) ” 
  &&  “ (has_right_2 <> 0) ”
  &&  ((( &( "has_left" ) )) # Int  |-> has_left_2)
  **  ((( &( "has_right" ) )) # Int  |-> has_right_2)
  **  ((( &( "left_best" ) )) # Int  |-> left_best_2)
  **  ((( &( "left_value" ) )) # Int  |-> left_value_2)
  **  ((( &( "right_value" ) )) # Int  |-> right_value_2)
  **  ((( &( "hsize" ) )) # Int  |-> hsize_3)
  **  ((( &( "total" ) )) # Int64  |-> total_3)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_3 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_3 )
  **  (IntArray.full heap_value_pre heap_cap vals_3 )
  **  (IntArray.full heap_start_pre heap_cap starts_3 )
  **  (IntArray.full heap_lo_pre heap_cap los_3 )
  **  (IntArray.full heap_hi_pre heap_cap his_3 )
  **  (IntArray.full heap_best_pre heap_cap bests_3 )
|--
  (EX (vals_out: (@list Z))  (starts_out: (@list Z))  (los_out: (@list Z))  (his_out: (@list Z))  (bests_out: (@list Z))  (slots_out: (@list ((((Z * Z) * Z) * Z) * Z)))  (chosen: (@list Z))  (total: Z)  (left_value: Z)  (left_best: Z)  (right_value: Z)  (hsize: Z)  (has_right: Z)  (has_left: Z)  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (has_left <> 0) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots hsize left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)))) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ” 
  &&  “ (has_right <> 0) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize + 1 ))
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots ))
  ||
  (EX (vals_out_2: (@list Z))  (starts_out_2: (@list Z))  (los_out_2: (@list Z))  (his_out_2: (@list Z))  (bests_out_2: (@list Z))  (slots_out_2: (@list ((((Z * Z) * Z) * Z) * Z)))  (chosen_2: (@list Z))  (total_2: Z)  (hsize_2: Z)  (vals_2: (@list Z))  (starts_2: (@list Z))  (los_2: (@list Z))  (his_2: (@list Z))  (bests_2: (@list Z))  (ans_2: Z)  (st_slots_2: (@list Z))  (ps_2: (@list Z))  (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (RangeArgmax ps_2 (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out_2 vals_out_2 starts_out_2 los_out_2 his_out_2 bests_out_2 ) ” 
  &&  “ (NodeHeapState slots_out_2 (hsize_2 - 1 ) ) ” 
  &&  “ (FrontierPopTop slots_2 hsize_2 slots_out_2 ) ” 
  &&  “ (value = (heap_top_value (slots_2))) ” 
  &&  “ (start = (heap_top_start (slots_2))) ” 
  &&  “ (lo = (heap_top_lo (slots_2))) ” 
  &&  “ (hi = (heap_top_hi (slots_2))) ” 
  &&  “ (best = (heap_top_best (slots_2))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize_2) ” 
  &&  “ (hsize_2 <= heap_cap) ” 
  &&  “ ((hsize_2 + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps_2 n_pre L_pre R_pre chosen_2 t total_2 (sublist (0) (hsize_2) (slots_2)) ) ” 
  &&  “ (NodeHeapState slots_2 hsize_2 ) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
  **  ((( &( "right_value" ) )) # Int  |-> ((Znth right_best ps_2 0) - (Znth (start - 1 ) ps_2 0) ))
  **  ((( &( "has_right" ) )) # Int  |-> 1)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_out_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_out_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_out_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_out_2 )
  **  ((( &( "hsize" ) )) # Int  |-> (hsize_2 - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total_2 + value ))
  **  (IntArray.full arr_pre n_pre l ))
.

Definition superPiano_entail_wit_11_2 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (has_left <> 0) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots hsize left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)))) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ” 
  &&  “ (has_right <> 0) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize + 1 ))
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  (“ (has_left <> 0) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots hsize left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)))) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ” 
  &&  “ (has_right <> 0) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize + 1 ))
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots ))
  ||
  (EX (vals_out_2: (@list Z))  (starts_out_2: (@list Z))  (los_out_2: (@list Z))  (his_out_2: (@list Z))  (bests_out_2: (@list Z))  (slots_out_2: (@list ((((Z * Z) * Z) * Z) * Z)))  (chosen_2: (@list Z))  (total_2: Z)  (hsize_2: Z)  (vals_2: (@list Z))  (starts_2: (@list Z))  (los_2: (@list Z))  (his_2: (@list Z))  (bests_2: (@list Z))  (ans_2: Z)  (st_slots_2: (@list Z))  (ps_2: (@list Z))  (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (RangeArgmax ps_2 (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out_2 vals_out_2 starts_out_2 los_out_2 his_out_2 bests_out_2 ) ” 
  &&  “ (NodeHeapState slots_out_2 (hsize_2 - 1 ) ) ” 
  &&  “ (FrontierPopTop slots_2 hsize_2 slots_out_2 ) ” 
  &&  “ (value = (heap_top_value (slots_2))) ” 
  &&  “ (start = (heap_top_start (slots_2))) ” 
  &&  “ (lo = (heap_top_lo (slots_2))) ” 
  &&  “ (hi = (heap_top_hi (slots_2))) ” 
  &&  “ (best = (heap_top_best (slots_2))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize_2) ” 
  &&  “ (hsize_2 <= heap_cap) ” 
  &&  “ ((hsize_2 + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps_2 n_pre L_pre R_pre chosen_2 t total_2 (sublist (0) (hsize_2) (slots_2)) ) ” 
  &&  “ (NodeHeapState slots_2 hsize_2 ) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
  **  ((( &( "right_value" ) )) # Int  |-> ((Znth right_best ps_2 0) - (Znth (start - 1 ) ps_2 0) ))
  **  ((( &( "has_right" ) )) # Int  |-> 1)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_out_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_out_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_out_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_out_2 )
  **  ((( &( "hsize" ) )) # Int  |-> (hsize_2 - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total_2 + value ))
  **  (IntArray.full arr_pre n_pre l ))
.

Definition superPiano_entail_wit_11_3 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_3: (@list Z)) (ans_3: Z) (st_slots_3: (@list Z)) (slots_3: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_3: (@list Z)) (starts_3: (@list Z)) (los_3: (@list Z)) (his_3: (@list Z)) (bests_3: (@list Z)) (chosen_3: (@list Z)) (heap_cap: Z) (has_left_2: Z) (has_right_2: Z) (t: Z) (hsize_3: Z) (left_best_2: Z) (best: Z) (lo: Z) (start: Z) (left_value_2: Z) (total_3: Z) (hi: Z) (right_best: Z) (right_value_2: Z) (value: Z) (vals_out_3: (@list Z)) (starts_out_3: (@list Z)) (los_out_3: (@list Z)) (his_out_3: (@list Z)) (bests_out_3: (@list Z)) (slots_out_3: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (has_left_2 <> 0) ” 
  &&  “ ((Zlength (slots_out_3)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out_3 vals_out_3 starts_out_3 los_out_3 his_out_3 bests_out_3 ) ” 
  &&  “ (NodeHeapState slots_out_3 (hsize_3 + 1 ) ) ” 
  &&  “ (FrontierPushFields slots_3 hsize_3 left_value_2 start lo (best - 1 ) left_best_2 slots_out_3 ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_3 ) ” 
  &&  “ (SparseArgmaxBuilt ps_3 st_slots_3 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_3 n_pre L_pre R_pre k_pre ans_3 ) ” 
  &&  “ ((Zlength (slots_3)) = heap_cap) ” 
  &&  “ (NodeArrays slots_3 vals_3 starts_3 los_3 his_3 bests_3 ) ” 
  &&  “ (has_left_2 = 1) ” 
  &&  “ (has_right_2 = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize_3) ” 
  &&  “ (hsize_3 < heap_cap) ” 
  &&  “ (((hsize_3 + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps_3 n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_3)) (t + 1 ) total_3 (cons ((mkNode (left_value_2) (start) (lo) ((best - 1 )) (left_best_2))) (nil)) (sublist (0) (hsize_3) (slots_3)) ) ” 
  &&  “ (NodeHeapState slots_3 hsize_3 ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps_3 lo (best - 1 ) left_best_2 ) ” 
  &&  “ (0 <= left_best_2) ” 
  &&  “ (left_best_2 < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best_2) ” 
  &&  “ (left_best_2 <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps_3 n_pre L_pre R_pre left_value_2 start lo (best - 1 ) left_best_2 ) ” 
  &&  “ (hi <= best) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value_2 = 0) ” 
  &&  “ (ValidNodeFields ps_3 n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < n_pre)) -> (((-1000) <= (Znth idx_3 l 0)) /\ ((Znth idx_3 l 0) <= 1000))) ” 
  &&  “ (has_right_2 <> 0) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out_3 )
  **  (IntArray.full heap_start_pre heap_cap starts_out_3 )
  **  (IntArray.full heap_lo_pre heap_cap los_out_3 )
  **  (IntArray.full heap_hi_pre heap_cap his_out_3 )
  **  (IntArray.full heap_best_pre heap_cap bests_out_3 )
  **  ((( &( "has_left" ) )) # Int  |-> has_left_2)
  **  ((( &( "has_right" ) )) # Int  |-> has_right_2)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize_3 + 1 ))
  **  ((( &( "left_best" ) )) # Int  |-> left_best_2)
  **  ((( &( "left_value" ) )) # Int  |-> left_value_2)
  **  ((( &( "total" ) )) # Int64  |-> total_3)
  **  ((( &( "right_value" ) )) # Int  |-> right_value_2)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_3 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_3 )
|--
  (EX (vals_out: (@list Z))  (starts_out: (@list Z))  (los_out: (@list Z))  (his_out: (@list Z))  (bests_out: (@list Z))  (slots_out: (@list ((((Z * Z) * Z) * Z) * Z)))  (chosen: (@list Z))  (total: Z)  (left_value: Z)  (left_best: Z)  (right_value: Z)  (hsize: Z)  (has_right: Z)  (has_left: Z)  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (has_left <> 0) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots hsize left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)))) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ” 
  &&  “ (has_right <> 0) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize + 1 ))
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots ))
  ||
  (EX (vals_out_2: (@list Z))  (starts_out_2: (@list Z))  (los_out_2: (@list Z))  (his_out_2: (@list Z))  (bests_out_2: (@list Z))  (slots_out_2: (@list ((((Z * Z) * Z) * Z) * Z)))  (chosen_2: (@list Z))  (total_2: Z)  (hsize_2: Z)  (vals_2: (@list Z))  (starts_2: (@list Z))  (los_2: (@list Z))  (his_2: (@list Z))  (bests_2: (@list Z))  (ans_2: Z)  (st_slots_2: (@list Z))  (ps_2: (@list Z))  (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (RangeArgmax ps_2 (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out_2 vals_out_2 starts_out_2 los_out_2 his_out_2 bests_out_2 ) ” 
  &&  “ (NodeHeapState slots_out_2 (hsize_2 - 1 ) ) ” 
  &&  “ (FrontierPopTop slots_2 hsize_2 slots_out_2 ) ” 
  &&  “ (value = (heap_top_value (slots_2))) ” 
  &&  “ (start = (heap_top_start (slots_2))) ” 
  &&  “ (lo = (heap_top_lo (slots_2))) ” 
  &&  “ (hi = (heap_top_hi (slots_2))) ” 
  &&  “ (best = (heap_top_best (slots_2))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize_2) ” 
  &&  “ (hsize_2 <= heap_cap) ” 
  &&  “ ((hsize_2 + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps_2 n_pre L_pre R_pre chosen_2 t total_2 (sublist (0) (hsize_2) (slots_2)) ) ” 
  &&  “ (NodeHeapState slots_2 hsize_2 ) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
  **  ((( &( "right_value" ) )) # Int  |-> ((Znth right_best ps_2 0) - (Znth (start - 1 ) ps_2 0) ))
  **  ((( &( "has_right" ) )) # Int  |-> 1)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_out_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_out_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_out_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_out_2 )
  **  ((( &( "hsize" ) )) # Int  |-> (hsize_2 - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total_2 + value ))
  **  (IntArray.full arr_pre n_pre l ))
.

Definition superPiano_entail_wit_11_4 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize_2: Z) (total: Z) (vals_out_2: (@list Z)) (starts_out_2: (@list Z)) (los_out_2: (@list Z)) (his_out_2: (@list Z)) (bests_out_2: (@list Z)) (slots_out_2: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ (RangeArgmax ps (best + 1 ) hi retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval) ” 
  &&  “ (retval <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out_2 vals_out_2 starts_out_2 los_out_2 his_out_2 bests_out_2 ) ” 
  &&  “ (NodeHeapState slots_out_2 (hsize_2 - 1 ) ) ” 
  &&  “ (FrontierPopTop slots_2 hsize_2 slots_out_2 ) ” 
  &&  “ (value = (heap_top_value (slots_2))) ” 
  &&  “ (start = (heap_top_start (slots_2))) ” 
  &&  “ (lo = (heap_top_lo (slots_2))) ” 
  &&  “ (hi = (heap_top_hi (slots_2))) ” 
  &&  “ (best = (heap_top_best (slots_2))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize_2) ” 
  &&  “ (hsize_2 <= heap_cap) ” 
  &&  “ ((hsize_2 + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen_2 t total (sublist (0) (hsize_2) (slots_2)) ) ” 
  &&  “ (NodeHeapState slots_2 hsize_2 ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
  **  (IntArray.full heap_value_pre heap_cap vals_out_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_out_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_out_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_out_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_out_2 )
  **  ((( &( "hsize" ) )) # Int  |-> (hsize_2 - 1 ))
  **  (IntArray.full arr_pre n_pre l )
|--
  (EX (vals_out: (@list Z))  (starts_out: (@list Z))  (los_out: (@list Z))  (his_out: (@list Z))  (bests_out: (@list Z))  (slots_out: (@list ((((Z * Z) * Z) * Z) * Z)))  (chosen: (@list Z))  (hsize: Z)  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps_2: (@list Z)) ,
  “ (0 <> 0) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots hsize 0 start lo (best - 1 ) 0 slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 = 1) ” 
  &&  “ (1 = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps_2 n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) (total + value ) (cons ((mkNode (0) (start) (lo) ((best - 1 )) (0))) ((cons ((mkNode (((Znth retval ps 0) - (Znth (start - 1 ) ps 0) )) (start) ((best + 1 )) (hi) (retval))) (nil)))) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps_2 lo (best - 1 ) 0 ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < (n_pre + 1 )) ” 
  &&  “ (lo <= 0) ” 
  &&  “ (0 <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre 0 start lo (best - 1 ) 0 ) ” 
  &&  “ (RangeArgmax ps_2 (best + 1 ) hi retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval) ” 
  &&  “ (retval <= hi) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre ((Znth retval ps 0) - (Znth (start - 1 ) ps 0) ) start (best + 1 ) hi retval ) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ” 
  &&  “ (1 <> 0) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "hsize" ) )) # Int  |-> (hsize + 1 ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots ))
  ||
  (“ (RangeArgmax ps (best + 1 ) hi retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval) ” 
  &&  “ (retval <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out_2 vals_out_2 starts_out_2 los_out_2 his_out_2 bests_out_2 ) ” 
  &&  “ (NodeHeapState slots_out_2 (hsize_2 - 1 ) ) ” 
  &&  “ (FrontierPopTop slots_2 hsize_2 slots_out_2 ) ” 
  &&  “ (value = (heap_top_value (slots_2))) ” 
  &&  “ (start = (heap_top_start (slots_2))) ” 
  &&  “ (lo = (heap_top_lo (slots_2))) ” 
  &&  “ (hi = (heap_top_hi (slots_2))) ” 
  &&  “ (best = (heap_top_best (slots_2))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize_2) ” 
  &&  “ (hsize_2 <= heap_cap) ” 
  &&  “ ((hsize_2 + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen_2 t total (sublist (0) (hsize_2) (slots_2)) ) ” 
  &&  “ (NodeHeapState slots_2 hsize_2 ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
  **  (IntArray.full heap_value_pre heap_cap vals_out_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_out_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_out_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_out_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_out_2 )
  **  ((( &( "hsize" ) )) # Int  |-> (hsize_2 - 1 ))
  **  (IntArray.full arr_pre n_pre l ))
.

Definition superPiano_entail_wit_12_1 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ (RangeArgmax ps (best + 1 ) hi retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval) ” 
  &&  “ (retval <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (RangeArgmax ps (best + 1 ) hi retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval) ” 
  &&  “ (retval <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_entail_wit_12_2 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize_2: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total_2: Z) (value: Z) (vals_out_2: (@list Z)) (starts_out_2: (@list Z)) (los_out_2: (@list Z)) (his_out_2: (@list Z)) (bests_out_2: (@list Z)) (slots_out_2: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (has_left <> 0) ” 
  &&  “ ((Zlength (slots_out_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out_2 vals_out_2 starts_out_2 los_out_2 his_out_2 bests_out_2 ) ” 
  &&  “ (NodeHeapState slots_out_2 (hsize_2 + 1 ) ) ” 
  &&  “ (FrontierPushFields slots_2 hsize_2 left_value start lo (best - 1 ) left_best slots_out_2 ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize_2) ” 
  &&  “ (hsize_2 < heap_cap) ” 
  &&  “ (((hsize_2 + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps_2 n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total_2 (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)))) (sublist (0) (hsize_2) (slots_2)) ) ” 
  &&  “ (NodeHeapState slots_2 hsize_2 ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps_2 lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (RangeArgmax ps_2 (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ” 
  &&  “ (has_right <> 0) ” 
  &&  “ (has_left = 0) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_out_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_out_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_out_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_out_2 )
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize_2 + 1 ))
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total_2)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
|--
  EX (vals_out: (@list Z))  (starts_out: (@list Z))  (los_out: (@list Z))  (his_out: (@list Z))  (bests_out: (@list Z))  (slots_out: (@list ((((Z * Z) * Z) * Z) * Z)))  (chosen: (@list Z))  (total: Z)  (hsize: Z)  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> ((Znth right_best ps 0) - (Znth (start - 1 ) ps 0) ))
  **  ((( &( "has_right" ) )) # Int  |-> 1)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_entail_wit_13 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (has_left <> 0) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots_2 hsize left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps_2 n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)))) (sublist (0) (hsize) (slots_2)) ) ” 
  &&  “ (NodeHeapState slots_2 hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps_2 lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (RangeArgmax ps_2 (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ” 
  &&  “ (has_right <> 0) ” 
  &&  “ (has_left <> 0) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= (hsize + 1 )) ” 
  &&  “ ((hsize + 1 ) < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)) (sublist (0) ((hsize + 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize + 1 ) ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
.

Definition superPiano_entail_wit_14 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ (RangeArgmax ps (best + 1 ) hi retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval) ” 
  &&  “ (retval <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots_2 hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots_2))) ” 
  &&  “ (start = (heap_top_start (slots_2))) ” 
  &&  “ (lo = (heap_top_lo (slots_2))) ” 
  &&  “ (hi = (heap_top_hi (slots_2))) ” 
  &&  “ (best = (heap_top_best (slots_2))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen_2 t total (sublist (0) (hsize) (slots_2)) ) ” 
  &&  “ (NodeHeapState slots_2 hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps_2: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (1 = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= (hsize - 1 )) ” 
  &&  “ ((hsize - 1 ) < heap_cap) ” 
  &&  “ ((((hsize - 1 ) + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps_2 n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) (total + value ) (cons ((mkNode (((Znth retval ps 0) - (Znth (start - 1 ) ps 0) )) (start) ((best + 1 )) (hi) (retval))) (nil)) (sublist (0) ((hsize - 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize - 1 ) ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ (RangeArgmax ps_2 (best + 1 ) hi retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval) ” 
  &&  “ (retval <= hi) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre ((Znth retval ps 0) - (Znth (start - 1 ) ps 0) ) start (best + 1 ) hi retval ) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
.

Definition superPiano_entail_wit_15_1 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (left_best: Z) (left_value: Z) (value: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots_2 hsize right_value start (best + 1 ) hi right_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps_2 n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)) (sublist (0) (hsize) (slots_2)) ) ” 
  &&  “ (NodeHeapState slots_2 hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ (RangeArgmax ps_2 (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps_2 lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= has_left) ” 
  &&  “ (has_left <= 1) ” 
  &&  “ (0 <= has_right) ” 
  &&  “ (has_right <= 1) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ (INT_MIN <= left_value) ” 
  &&  “ (left_value <= INT_MAX) ” 
  &&  “ (INT_MIN <= right_value) ” 
  &&  “ (right_value <= INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= (hsize + 1 )) ” 
  &&  “ ((hsize + 1 ) < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - (t + 1 ) ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (sublist (0) ((hsize + 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize + 1 ) ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
.

Definition superPiano_entail_wit_15_2 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (heap_cap: Z) (has_left: Z) (left_best: Z) (left_value: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (value: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots_2 hsize right_value start (best + 1 ) hi right_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (has_left = 0) ” 
  &&  “ (left_best = 0) ” 
  &&  “ (left_value = 0) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps_2 n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)) (sublist (0) (hsize) (slots_2)) ) ” 
  &&  “ (NodeHeapState slots_2 hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ (RangeArgmax ps_2 (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= has_left) ” 
  &&  “ (has_left <= 1) ” 
  &&  “ (0 <= has_right) ” 
  &&  “ (has_right <= 1) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ (INT_MIN <= left_value) ” 
  &&  “ (left_value <= INT_MAX) ” 
  &&  “ (INT_MIN <= right_value) ” 
  &&  “ (right_value <= INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= (hsize + 1 )) ” 
  &&  “ ((hsize + 1 ) < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - (t + 1 ) ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (sublist (0) ((hsize + 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize + 1 ) ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
.

Definition superPiano_entail_wit_15_3 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (left_best: Z) (best: Z) (lo: Z) (start: Z) (left_value: Z) (total: Z) (hi: Z) (right_best: Z) (right_value: Z) (value: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (has_left <> 0) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields slots_2 hsize left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps_2 n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) (nil)) (sublist (0) (hsize) (slots_2)) ) ” 
  &&  “ (NodeHeapState slots_2 hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps_2 lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (hi <= best) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ” 
  &&  “ (has_right = 0) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= has_left) ” 
  &&  “ (has_left <= 1) ” 
  &&  “ (0 <= has_right) ” 
  &&  “ (has_right <= 1) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ (INT_MIN <= left_value) ” 
  &&  “ (left_value <= INT_MAX) ” 
  &&  “ (INT_MIN <= right_value) ” 
  &&  “ (right_value <= INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= (hsize + 1 )) ” 
  &&  “ ((hsize + 1 ) < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - (t + 1 ) ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (sublist (0) ((hsize + 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize + 1 ) ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
.

Definition superPiano_entail_wit_15_4 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (left_best: Z) (left_value: Z) (right_best: Z) (right_value: Z) (t: Z) (hsize: Z) (total: Z) (best: Z) (start: Z) (lo: Z) (hi: Z) (value: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (has_left = 0) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (left_best = 0) ” 
  &&  “ (left_value = 0) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((hsize + (k_pre - (t + 1 ) ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps_2 n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total nil (sublist (0) (hsize) (slots_2)) ) ” 
  &&  “ (NodeHeapState slots_2 hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (lo = best) ” 
  &&  “ (best = hi) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ” 
  &&  “ (has_right = 0) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
  **  (IntArray.full heap_value_pre heap_cap vals_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_2 )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= has_left) ” 
  &&  “ (has_left <= 1) ” 
  &&  “ (0 <= has_right) ” 
  &&  “ (has_right <= 1) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ (INT_MIN <= left_value) ” 
  &&  “ (left_value <= INT_MAX) ” 
  &&  “ (INT_MIN <= right_value) ” 
  &&  “ (right_value <= INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((hsize + (k_pre - (t + 1 ) ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
.

Definition superPiano_entail_wit_16 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (left_best: Z) (right_best: Z) (left_value: Z) (right_value: Z) (t: Z) (hsize: Z) (total: Z) (best: Z) (start: Z) (hi: Z) (lo: Z) (value: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (0 <= has_left) ” 
  &&  “ (has_left <= 1) ” 
  &&  “ (0 <= has_right) ” 
  &&  “ (has_right <= 1) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ (INT_MIN <= left_value) ” 
  &&  “ (left_value <= INT_MAX) ” 
  &&  “ (INT_MIN <= right_value) ” 
  &&  “ (right_value <= INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((hsize + (k_pre - (t + 1 ) ) ) < heap_cap) ” 
  &&  “ (FrontierState ps_2 n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (sublist (0) (hsize) (slots_2)) ) ” 
  &&  “ (NodeHeapState slots_2 hsize ) ” 
  &&  “ (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
  **  (IntArray.full heap_value_pre heap_cap vals_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_2 )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - (t + 1 ) ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen (t + 1 ) total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (((t + 1 ) < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
.

Definition superPiano_return_wit_1 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (chosen: (@list Z)) (total: Z) (hsize: Z) (t: Z) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (ans: Z) (st_slots_2: (@list Z)) (ps_2: (@list Z)) (heap_cap: Z) ,
  “ (t >= k_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps_2 n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots_2)) ) ” 
  &&  “ (NodeHeapState slots_2 hsize ) ” 
  &&  “ ((t < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
  **  (IntArray.full heap_value_pre heap_cap vals_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_2 )
|--
  EX (st_slots: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ps: (@list Z)) ,
  “ (PrefixSums l ps ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre total ) ” 
  &&  “ ((Zlength (slots)) = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre ((n_pre + k_pre ) + 1 ) vals )
  **  (IntArray.full heap_start_pre ((n_pre + k_pre ) + 1 ) starts )
  **  (IntArray.full heap_lo_pre ((n_pre + k_pre ) + 1 ) los )
  **  (IntArray.full heap_hi_pre ((n_pre + k_pre ) + 1 ) his )
  **  (IntArray.full heap_best_pre ((n_pre + k_pre ) + 1 ) bests )
.

Definition superPiano_partial_solve_wit_1_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_3 ps 0)) /\ ((Znth idx_3 ps 0) <= INT_MAX))) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((-9223372036854775808) <= ans) ” 
  &&  “ (ans <= 9223372036854775807) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l 0)) /\ ((Znth idx_4 l 0) <= 1000))) ”
  &&  ((( &( "heap_cap" ) )) # Int  |-> ((n_pre + k_pre ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_full prefix_pre (n_pre + 1 ) )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_start_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_lo_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_hi_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_best_pre ((n_pre + k_pre ) + 1 ) )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
.

Definition superPiano_partial_solve_wit_1_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_3 ps 0)) /\ ((Znth idx_3 ps 0) <= INT_MAX))) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((-9223372036854775808) <= ans) ” 
  &&  “ (ans <= 9223372036854775807) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l 0)) /\ ((Znth idx_4 l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_full prefix_pre (n_pre + 1 ) )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_start_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_lo_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_hi_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_best_pre ((n_pre + k_pre ) + 1 ) )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_3 ps 0)) /\ ((Znth idx_3 ps 0) <= INT_MAX))) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((-9223372036854775808) <= ans) ” 
  &&  “ (ans <= 9223372036854775807) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l 0)) /\ ((Znth idx_4 l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_full prefix_pre (n_pre + 1 ) )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_start_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_lo_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_hi_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_best_pre ((n_pre + k_pre ) + 1 ) )
.

Definition superPiano_partial_solve_wit_1 := superPiano_partial_solve_wit_1_pure -> superPiano_partial_solve_wit_1_aux.

Definition superPiano_partial_solve_wit_2_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (heap_cap: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ ((Zlength (st_slots)) = ((n_pre + 1 ) * ST_LEVELS )) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
|--
  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) <= 100001) ” 
  &&  “ ((Zlength (ps)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (st_slots)) = ((n_pre + 1 ) * ST_LEVELS )) ” 
  &&  “ ((Zlength (ps)) = ((Zlength (l)) + 1 )) ”
.

Definition superPiano_partial_solve_wit_2_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (heap_cap: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ ((Zlength (st_slots)) = ((n_pre + 1 ) * ST_LEVELS )) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
|--
  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) <= 100001) ” 
  &&  “ ((Zlength (ps)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (st_slots)) = ((n_pre + 1 ) * ST_LEVELS )) ” 
  &&  “ ((Zlength (ps)) = ((Zlength (l)) + 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ ((Zlength (st_slots)) = ((n_pre + 1 ) * ST_LEVELS )) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
.

Definition superPiano_partial_solve_wit_2 := superPiano_partial_solve_wit_2_pure -> superPiano_partial_solve_wit_2_aux.

Definition superPiano_partial_solve_wit_3_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (heap_cap: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  ((( &( "hsize" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (((n_pre - L_pre ) + 1 ) <= heap_cap) ” 
  &&  “ ((Zlength (ps)) = (n_pre + 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((Zlength (ps)) = ((Zlength (l)) + 1 )) ”
.

Definition superPiano_partial_solve_wit_3_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (heap_cap: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (((n_pre - L_pre ) + 1 ) <= heap_cap) ” 
  &&  “ ((Zlength (ps)) = (n_pre + 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((Zlength (ps)) = ((Zlength (l)) + 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_partial_solve_wit_3 := superPiano_partial_solve_wit_3_pure -> superPiano_partial_solve_wit_3_aux.

Definition superPiano_partial_solve_wit_4_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (chosen: (@list Z)) (total: Z) (hsize: Z) (t: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (ans: Z) (st_slots: (@list Z)) (ps: (@list Z)) (heap_cap: Z) ,
  “ (t < k_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ ((t < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "value" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ”
.

Definition superPiano_partial_solve_wit_4_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (chosen: (@list Z)) (total: Z) (hsize: Z) (t: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (ans: Z) (st_slots: (@list Z)) (ps: (@list Z)) (heap_cap: Z) ,
  “ (t < k_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ ((t < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ ((t < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
.

Definition superPiano_partial_solve_wit_4 := superPiano_partial_solve_wit_4_pure -> superPiano_partial_solve_wit_4_aux.

Definition superPiano_partial_solve_wit_5_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (chosen: (@list Z)) (total: Z) (hsize: Z) (t: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (ans: Z) (st_slots: (@list Z)) (ps: (@list Z)) (heap_cap: Z) (retval: Z) ,
  “ (retval = (heap_top_value (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ ((t < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "start" ) )) # Int  |->_)
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  ((( &( "value" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ”
.

Definition superPiano_partial_solve_wit_5_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (chosen: (@list Z)) (total: Z) (hsize: Z) (t: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (ans: Z) (st_slots: (@list Z)) (ps: (@list Z)) (heap_cap: Z) (retval: Z) ,
  “ (retval = (heap_top_value (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ ((t < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval = (heap_top_value (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ ((t < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
.

Definition superPiano_partial_solve_wit_5 := superPiano_partial_solve_wit_5_pure -> superPiano_partial_solve_wit_5_aux.

Definition superPiano_partial_solve_wit_6_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (chosen: (@list Z)) (total: Z) (hsize: Z) (t: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (ans: Z) (st_slots: (@list Z)) (ps: (@list Z)) (heap_cap: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 = (heap_top_start (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval = (heap_top_value (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ ((t < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "lo" ) )) # Int  |->_)
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  ((( &( "start" ) )) # Int  |-> retval_2)
  **  ((( &( "value" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ”
.

Definition superPiano_partial_solve_wit_6_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (chosen: (@list Z)) (total: Z) (hsize: Z) (t: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (ans: Z) (st_slots: (@list Z)) (ps: (@list Z)) (heap_cap: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 = (heap_top_start (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval = (heap_top_value (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ ((t < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval_2 = (heap_top_start (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval = (heap_top_value (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ ((t < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
.

Definition superPiano_partial_solve_wit_6 := superPiano_partial_solve_wit_6_pure -> superPiano_partial_solve_wit_6_aux.

Definition superPiano_partial_solve_wit_7_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (chosen: (@list Z)) (total: Z) (hsize: Z) (t: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (ans: Z) (st_slots: (@list Z)) (ps: (@list Z)) (heap_cap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  “ (retval_3 = (heap_top_lo (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval_2 = (heap_top_start (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval = (heap_top_value (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ ((t < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "hi" ) )) # Int  |->_)
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  ((( &( "lo" ) )) # Int  |-> retval_3)
  **  ((( &( "start" ) )) # Int  |-> retval_2)
  **  ((( &( "value" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ”
.

Definition superPiano_partial_solve_wit_7_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (chosen: (@list Z)) (total: Z) (hsize: Z) (t: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (ans: Z) (st_slots: (@list Z)) (ps: (@list Z)) (heap_cap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  “ (retval_3 = (heap_top_lo (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval_2 = (heap_top_start (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval = (heap_top_value (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ ((t < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval_3 = (heap_top_lo (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval_2 = (heap_top_start (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval = (heap_top_value (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ ((t < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
.

Definition superPiano_partial_solve_wit_7 := superPiano_partial_solve_wit_7_pure -> superPiano_partial_solve_wit_7_aux.

Definition superPiano_partial_solve_wit_8_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (chosen: (@list Z)) (total: Z) (hsize: Z) (t: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (ans: Z) (st_slots: (@list Z)) (ps: (@list Z)) (heap_cap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  “ (retval_4 = (heap_top_hi (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval_3 = (heap_top_lo (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval_2 = (heap_top_start (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval = (heap_top_value (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ ((t < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "best" ) )) # Int  |->_)
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  ((( &( "hi" ) )) # Int  |-> retval_4)
  **  ((( &( "lo" ) )) # Int  |-> retval_3)
  **  ((( &( "start" ) )) # Int  |-> retval_2)
  **  ((( &( "value" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ”
.

Definition superPiano_partial_solve_wit_8_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (chosen: (@list Z)) (total: Z) (hsize: Z) (t: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (ans: Z) (st_slots: (@list Z)) (ps: (@list Z)) (heap_cap: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  “ (retval_4 = (heap_top_hi (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval_3 = (heap_top_lo (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval_2 = (heap_top_start (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval = (heap_top_value (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ ((t < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval_4 = (heap_top_hi (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval_3 = (heap_top_lo (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval_2 = (heap_top_start (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval = (heap_top_value (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ ((t < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
.

Definition superPiano_partial_solve_wit_8 := superPiano_partial_solve_wit_8_pure -> superPiano_partial_solve_wit_8_aux.

Definition superPiano_partial_solve_wit_9_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) ,
  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ”
.

Definition superPiano_partial_solve_wit_9_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) ,
  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
.

Definition superPiano_partial_solve_wit_9 := superPiano_partial_solve_wit_9_pure -> superPiano_partial_solve_wit_9_aux.

Definition superPiano_partial_solve_wit_10_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) <= 100001) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best - 1 ) < (n_pre + 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ”
.

Definition superPiano_partial_solve_wit_10_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) <= 100001) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best - 1 ) < (n_pre + 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_partial_solve_wit_10 := superPiano_partial_solve_wit_10_pure -> superPiano_partial_solve_wit_10_aux.

Definition superPiano_partial_solve_wit_11 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (((prefix_pre + (retval * sizeof(INT) ) )) # Int  |-> (Znth retval ps 0))
  **  (IntArray.missing_i prefix_pre retval 0 (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_partial_solve_wit_12 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (((prefix_pre + ((start - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (start - 1 ) ps 0))
  **  (IntArray.missing_i prefix_pre (start - 1 ) 0 (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_partial_solve_wit_13_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ ((best + 1 ) <= hi) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval ps 0) - (Znth (start - 1 ) ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) <= 100001) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi < (n_pre + 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ”
.

Definition superPiano_partial_solve_wit_13_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ ((best + 1 ) <= hi) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) <= 100001) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi < (n_pre + 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_partial_solve_wit_13 := superPiano_partial_solve_wit_13_pure -> superPiano_partial_solve_wit_13_aux.

Definition superPiano_partial_solve_wit_14_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) <= 100001) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi < (n_pre + 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ”
.

Definition superPiano_partial_solve_wit_14_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) <= 100001) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi < (n_pre + 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_partial_solve_wit_14 := superPiano_partial_solve_wit_14_pure -> superPiano_partial_solve_wit_14_aux.

Definition superPiano_partial_solve_wit_15 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ (RangeArgmax ps (best + 1 ) hi retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval) ” 
  &&  “ (retval <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (RangeArgmax ps (best + 1 ) hi retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval) ” 
  &&  “ (retval <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (((prefix_pre + (retval * sizeof(INT) ) )) # Int  |-> (Znth retval ps 0))
  **  (IntArray.missing_i prefix_pre retval 0 (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_partial_solve_wit_16 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) ,
  “ (RangeArgmax ps (best + 1 ) hi retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval) ” 
  &&  “ (retval <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (RangeArgmax ps (best + 1 ) hi retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval) ” 
  &&  “ (retval <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (((prefix_pre + ((start - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (start - 1 ) ps 0))
  **  (IntArray.missing_i prefix_pre (start - 1 ) 0 (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_partial_solve_wit_17 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) (retval_2: Z) ,
  “ (RangeArgmax ps (best + 1 ) hi retval_2 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval_2) ” 
  &&  “ (retval_2 <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (RangeArgmax ps (best + 1 ) hi retval_2 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval_2) ” 
  &&  “ (retval_2 <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (((prefix_pre + (retval_2 * sizeof(INT) ) )) # Int  |-> (Znth retval_2 ps 0))
  **  (IntArray.missing_i prefix_pre retval_2 0 (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_partial_solve_wit_18 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) (retval_2: Z) ,
  “ (RangeArgmax ps (best + 1 ) hi retval_2 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval_2) ” 
  &&  “ (retval_2 <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (RangeArgmax ps (best + 1 ) hi retval_2 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval_2) ” 
  &&  “ (retval_2 <= hi) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (slots))) ” 
  &&  “ (start = (heap_top_start (slots))) ” 
  &&  “ (lo = (heap_top_lo (slots))) ” 
  &&  “ (hi = (heap_top_hi (slots))) ” 
  &&  “ (best = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (((prefix_pre + ((start - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (start - 1 ) ps 0))
  **  (IntArray.missing_i prefix_pre (start - 1 ) 0 (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_partial_solve_wit_19_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (left_best: Z) (best: Z) (lo: Z) (start: Z) (left_value: Z) (total: Z) (hi: Z) (right_best: Z) (right_value: Z) (value: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) (nil)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (hi <= best) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ”
.

Definition superPiano_partial_solve_wit_19_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (left_best: Z) (best: Z) (lo: Z) (start: Z) (left_value: Z) (total: Z) (hi: Z) (right_best: Z) (right_value: Z) (value: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) (nil)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (hi <= best) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) (nil)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (hi <= best) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
.

Definition superPiano_partial_solve_wit_19 := superPiano_partial_solve_wit_19_pure -> superPiano_partial_solve_wit_19_aux.

Definition superPiano_partial_solve_wit_20_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)))) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ”
.

Definition superPiano_partial_solve_wit_20_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)))) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)))) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
.

Definition superPiano_partial_solve_wit_20 := superPiano_partial_solve_wit_20_pure -> superPiano_partial_solve_wit_20_aux.

Definition superPiano_partial_solve_wit_21_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (left_best: Z) (left_value: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (value: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 0) ” 
  &&  “ (left_best = 0) ” 
  &&  “ (left_value = 0) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ”
.

Definition superPiano_partial_solve_wit_21_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (left_best: Z) (left_value: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (value: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 0) ” 
  &&  “ (left_best = 0) ” 
  &&  “ (left_value = 0) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 0) ” 
  &&  “ (left_best = 0) ” 
  &&  “ (left_value = 0) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
.

Definition superPiano_partial_solve_wit_21 := superPiano_partial_solve_wit_21_pure -> superPiano_partial_solve_wit_21_aux.

Definition superPiano_partial_solve_wit_22_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (left_best: Z) (left_value: Z) (value: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ”
.

Definition superPiano_partial_solve_wit_22_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (left_best: Z) (left_value: Z) (value: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) (nil)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
.

Definition superPiano_partial_solve_wit_22 := superPiano_partial_solve_wit_22_pure -> superPiano_partial_solve_wit_22_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_build_prefix_safety_wit_1 : build_prefix_safety_wit_1.
Axiom proof_of_build_prefix_safety_wit_2 : build_prefix_safety_wit_2.
Axiom proof_of_build_prefix_safety_wit_3 : build_prefix_safety_wit_3.
Axiom proof_of_build_prefix_safety_wit_4 : build_prefix_safety_wit_4.
Axiom proof_of_build_prefix_safety_wit_5 : build_prefix_safety_wit_5.
Axiom proof_of_build_prefix_safety_wit_6 : build_prefix_safety_wit_6.
Axiom proof_of_build_prefix_safety_wit_7 : build_prefix_safety_wit_7.
Axiom proof_of_build_prefix_entail_wit_1 : build_prefix_entail_wit_1.
Axiom proof_of_build_prefix_entail_wit_2 : build_prefix_entail_wit_2.
Axiom proof_of_build_prefix_entail_wit_3 : build_prefix_entail_wit_3.
Axiom proof_of_build_prefix_return_wit_1 : build_prefix_return_wit_1.
Axiom proof_of_build_prefix_partial_solve_wit_1 : build_prefix_partial_solve_wit_1.
Axiom proof_of_build_prefix_partial_solve_wit_2 : build_prefix_partial_solve_wit_2.
Axiom proof_of_build_prefix_partial_solve_wit_3 : build_prefix_partial_solve_wit_3.
Axiom proof_of_build_prefix_partial_solve_wit_4 : build_prefix_partial_solve_wit_4.
Axiom proof_of_superPiano_safety_wit_1 : superPiano_safety_wit_1.
Axiom proof_of_superPiano_safety_wit_2 : superPiano_safety_wit_2.
Axiom proof_of_superPiano_safety_wit_3 : superPiano_safety_wit_3.
Axiom proof_of_superPiano_safety_wit_4 : superPiano_safety_wit_4.
Axiom proof_of_superPiano_safety_wit_5 : superPiano_safety_wit_5.
Axiom proof_of_superPiano_safety_wit_6 : superPiano_safety_wit_6.
Axiom proof_of_superPiano_safety_wit_7 : superPiano_safety_wit_7.
Axiom proof_of_superPiano_safety_wit_8 : superPiano_safety_wit_8.
Axiom proof_of_superPiano_safety_wit_9 : superPiano_safety_wit_9.
Axiom proof_of_superPiano_safety_wit_10 : superPiano_safety_wit_10.
Axiom proof_of_superPiano_safety_wit_11 : superPiano_safety_wit_11.
Axiom proof_of_superPiano_safety_wit_12 : superPiano_safety_wit_12.
Axiom proof_of_superPiano_safety_wit_13 : superPiano_safety_wit_13.
Axiom proof_of_superPiano_safety_wit_14 : superPiano_safety_wit_14.
Axiom proof_of_superPiano_safety_wit_15 : superPiano_safety_wit_15.
Axiom proof_of_superPiano_safety_wit_16 : superPiano_safety_wit_16.
Axiom proof_of_superPiano_safety_wit_17 : superPiano_safety_wit_17.
Axiom proof_of_superPiano_safety_wit_18 : superPiano_safety_wit_18.
Axiom proof_of_superPiano_safety_wit_19 : superPiano_safety_wit_19.
Axiom proof_of_superPiano_safety_wit_20 : superPiano_safety_wit_20.
Axiom proof_of_superPiano_safety_wit_21 : superPiano_safety_wit_21.
Axiom proof_of_superPiano_safety_wit_22 : superPiano_safety_wit_22.
Axiom proof_of_superPiano_safety_wit_23 : superPiano_safety_wit_23.
Axiom proof_of_superPiano_safety_wit_24 : superPiano_safety_wit_24.
Axiom proof_of_superPiano_safety_wit_25 : superPiano_safety_wit_25.
Axiom proof_of_superPiano_safety_wit_26 : superPiano_safety_wit_26.
Axiom proof_of_superPiano_safety_wit_27 : superPiano_safety_wit_27.
Axiom proof_of_superPiano_safety_wit_28 : superPiano_safety_wit_28.
Axiom proof_of_superPiano_safety_wit_29 : superPiano_safety_wit_29.
Axiom proof_of_superPiano_safety_wit_30 : superPiano_safety_wit_30.
Axiom proof_of_superPiano_safety_wit_31 : superPiano_safety_wit_31.
Axiom proof_of_superPiano_safety_wit_32 : superPiano_safety_wit_32.
Axiom proof_of_superPiano_safety_wit_33 : superPiano_safety_wit_33.
Axiom proof_of_superPiano_safety_wit_34 : superPiano_safety_wit_34.
Axiom proof_of_superPiano_safety_wit_35 : superPiano_safety_wit_35.
Axiom proof_of_superPiano_safety_wit_36 : superPiano_safety_wit_36.
Axiom proof_of_superPiano_safety_wit_37 : superPiano_safety_wit_37.
Axiom proof_of_superPiano_safety_wit_38 : superPiano_safety_wit_38.
Axiom proof_of_superPiano_safety_wit_39 : superPiano_safety_wit_39.
Axiom proof_of_superPiano_safety_wit_40 : superPiano_safety_wit_40.
Axiom proof_of_superPiano_safety_wit_41 : superPiano_safety_wit_41.
Axiom proof_of_superPiano_safety_wit_42 : superPiano_safety_wit_42.
Axiom proof_of_superPiano_safety_wit_43 : superPiano_safety_wit_43.
Axiom proof_of_superPiano_safety_wit_44 : superPiano_safety_wit_44.
Axiom proof_of_superPiano_safety_wit_45 : superPiano_safety_wit_45.
Axiom proof_of_superPiano_safety_wit_46 : superPiano_safety_wit_46.
Axiom proof_of_superPiano_safety_wit_47 : superPiano_safety_wit_47.
Axiom proof_of_superPiano_safety_wit_48 : superPiano_safety_wit_48.
Axiom proof_of_superPiano_safety_wit_49 : superPiano_safety_wit_49.
Axiom proof_of_superPiano_safety_wit_50 : superPiano_safety_wit_50.
Axiom proof_of_superPiano_safety_wit_51 : superPiano_safety_wit_51.
Axiom proof_of_superPiano_safety_wit_52 : superPiano_safety_wit_52.
Axiom proof_of_superPiano_safety_wit_53 : superPiano_safety_wit_53.
Axiom proof_of_superPiano_safety_wit_54 : superPiano_safety_wit_54.
Axiom proof_of_superPiano_safety_wit_55 : superPiano_safety_wit_55.
Axiom proof_of_superPiano_safety_wit_56 : superPiano_safety_wit_56.
Axiom proof_of_superPiano_safety_wit_57 : superPiano_safety_wit_57.
Axiom proof_of_superPiano_safety_wit_58 : superPiano_safety_wit_58.
Axiom proof_of_superPiano_safety_wit_59 : superPiano_safety_wit_59.
Axiom proof_of_superPiano_safety_wit_60 : superPiano_safety_wit_60.
Axiom proof_of_superPiano_safety_wit_61 : superPiano_safety_wit_61.
Axiom proof_of_superPiano_safety_wit_62 : superPiano_safety_wit_62.
Axiom proof_of_superPiano_safety_wit_63 : superPiano_safety_wit_63.
Axiom proof_of_superPiano_safety_wit_64 : superPiano_safety_wit_64.
Axiom proof_of_superPiano_safety_wit_65 : superPiano_safety_wit_65.
Axiom proof_of_superPiano_safety_wit_66 : superPiano_safety_wit_66.
Axiom proof_of_superPiano_safety_wit_67 : superPiano_safety_wit_67.
Axiom proof_of_superPiano_safety_wit_68 : superPiano_safety_wit_68.
Axiom proof_of_superPiano_safety_wit_69 : superPiano_safety_wit_69.
Axiom proof_of_superPiano_entail_wit_1 : superPiano_entail_wit_1.
Axiom proof_of_superPiano_entail_wit_2 : superPiano_entail_wit_2.
Axiom proof_of_superPiano_entail_wit_3 : superPiano_entail_wit_3.
Axiom proof_of_superPiano_entail_wit_4 : superPiano_entail_wit_4.
Axiom proof_of_superPiano_entail_wit_5 : superPiano_entail_wit_5.
Axiom proof_of_superPiano_entail_wit_6 : superPiano_entail_wit_6.
Axiom proof_of_superPiano_entail_wit_7 : superPiano_entail_wit_7.
Axiom proof_of_superPiano_entail_wit_8 : superPiano_entail_wit_8.
Axiom proof_of_superPiano_entail_wit_9 : superPiano_entail_wit_9.
Axiom proof_of_superPiano_entail_wit_10_1 : superPiano_entail_wit_10_1.
Axiom proof_of_superPiano_entail_wit_10_2 : superPiano_entail_wit_10_2.
Axiom proof_of_superPiano_entail_wit_10_3 : superPiano_entail_wit_10_3.
Axiom proof_of_superPiano_entail_wit_11_1 : superPiano_entail_wit_11_1.
Axiom proof_of_superPiano_entail_wit_11_2 : superPiano_entail_wit_11_2.
Axiom proof_of_superPiano_entail_wit_11_3 : superPiano_entail_wit_11_3.
Axiom proof_of_superPiano_entail_wit_11_4 : superPiano_entail_wit_11_4.
Axiom proof_of_superPiano_entail_wit_12_1 : superPiano_entail_wit_12_1.
Axiom proof_of_superPiano_entail_wit_12_2 : superPiano_entail_wit_12_2.
Axiom proof_of_superPiano_entail_wit_13 : superPiano_entail_wit_13.
Axiom proof_of_superPiano_entail_wit_14 : superPiano_entail_wit_14.
Axiom proof_of_superPiano_entail_wit_15_1 : superPiano_entail_wit_15_1.
Axiom proof_of_superPiano_entail_wit_15_2 : superPiano_entail_wit_15_2.
Axiom proof_of_superPiano_entail_wit_15_3 : superPiano_entail_wit_15_3.
Axiom proof_of_superPiano_entail_wit_15_4 : superPiano_entail_wit_15_4.
Axiom proof_of_superPiano_entail_wit_16 : superPiano_entail_wit_16.
Axiom proof_of_superPiano_return_wit_1 : superPiano_return_wit_1.
Axiom proof_of_superPiano_partial_solve_wit_1_pure : superPiano_partial_solve_wit_1_pure.
Axiom proof_of_superPiano_partial_solve_wit_1 : superPiano_partial_solve_wit_1.
Axiom proof_of_superPiano_partial_solve_wit_2_pure : superPiano_partial_solve_wit_2_pure.
Axiom proof_of_superPiano_partial_solve_wit_2 : superPiano_partial_solve_wit_2.
Axiom proof_of_superPiano_partial_solve_wit_3_pure : superPiano_partial_solve_wit_3_pure.
Axiom proof_of_superPiano_partial_solve_wit_3 : superPiano_partial_solve_wit_3.
Axiom proof_of_superPiano_partial_solve_wit_4_pure : superPiano_partial_solve_wit_4_pure.
Axiom proof_of_superPiano_partial_solve_wit_4 : superPiano_partial_solve_wit_4.
Axiom proof_of_superPiano_partial_solve_wit_5_pure : superPiano_partial_solve_wit_5_pure.
Axiom proof_of_superPiano_partial_solve_wit_5 : superPiano_partial_solve_wit_5.
Axiom proof_of_superPiano_partial_solve_wit_6_pure : superPiano_partial_solve_wit_6_pure.
Axiom proof_of_superPiano_partial_solve_wit_6 : superPiano_partial_solve_wit_6.
Axiom proof_of_superPiano_partial_solve_wit_7_pure : superPiano_partial_solve_wit_7_pure.
Axiom proof_of_superPiano_partial_solve_wit_7 : superPiano_partial_solve_wit_7.
Axiom proof_of_superPiano_partial_solve_wit_8_pure : superPiano_partial_solve_wit_8_pure.
Axiom proof_of_superPiano_partial_solve_wit_8 : superPiano_partial_solve_wit_8.
Axiom proof_of_superPiano_partial_solve_wit_9_pure : superPiano_partial_solve_wit_9_pure.
Axiom proof_of_superPiano_partial_solve_wit_9 : superPiano_partial_solve_wit_9.
Axiom proof_of_superPiano_partial_solve_wit_10_pure : superPiano_partial_solve_wit_10_pure.
Axiom proof_of_superPiano_partial_solve_wit_10 : superPiano_partial_solve_wit_10.
Axiom proof_of_superPiano_partial_solve_wit_11 : superPiano_partial_solve_wit_11.
Axiom proof_of_superPiano_partial_solve_wit_12 : superPiano_partial_solve_wit_12.
Axiom proof_of_superPiano_partial_solve_wit_13_pure : superPiano_partial_solve_wit_13_pure.
Axiom proof_of_superPiano_partial_solve_wit_13 : superPiano_partial_solve_wit_13.
Axiom proof_of_superPiano_partial_solve_wit_14_pure : superPiano_partial_solve_wit_14_pure.
Axiom proof_of_superPiano_partial_solve_wit_14 : superPiano_partial_solve_wit_14.
Axiom proof_of_superPiano_partial_solve_wit_15 : superPiano_partial_solve_wit_15.
Axiom proof_of_superPiano_partial_solve_wit_16 : superPiano_partial_solve_wit_16.
Axiom proof_of_superPiano_partial_solve_wit_17 : superPiano_partial_solve_wit_17.
Axiom proof_of_superPiano_partial_solve_wit_18 : superPiano_partial_solve_wit_18.
Axiom proof_of_superPiano_partial_solve_wit_19_pure : superPiano_partial_solve_wit_19_pure.
Axiom proof_of_superPiano_partial_solve_wit_19 : superPiano_partial_solve_wit_19.
Axiom proof_of_superPiano_partial_solve_wit_20_pure : superPiano_partial_solve_wit_20_pure.
Axiom proof_of_superPiano_partial_solve_wit_20 : superPiano_partial_solve_wit_20.
Axiom proof_of_superPiano_partial_solve_wit_21_pure : superPiano_partial_solve_wit_21_pure.
Axiom proof_of_superPiano_partial_solve_wit_21 : superPiano_partial_solve_wit_21.
Axiom proof_of_superPiano_partial_solve_wit_22_pure : superPiano_partial_solve_wit_22_pure.
Axiom proof_of_superPiano_partial_solve_wit_22 : superPiano_partial_solve_wit_22.

End VC_Correct.
