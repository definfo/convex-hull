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
Require Import SimpleC.EE.Applications_human.minigmp.GmpAux SimpleC.EE.Applications_human.minigmp.GmpNumber.
Import Aux.
Local Open Scope sac.
Require Import gmp_strategy_goal.
Require Import gmp_strategy_proof.

(*----- Function gmp_abs -----*)

Definition gmp_abs_safety_wit_1 := 
forall (x_pre: Z) ,
  “ (INT_MIN < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ”
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition gmp_abs_safety_wit_2 := 
forall (x_pre: Z) ,
  “ (x_pre < 0) ” 
  &&  “ (INT_MIN < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ”
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (x_pre <> (INT_MIN)) ”
.

Definition gmp_abs_return_wit_1 := 
forall (x_pre: Z) ,
  “ (x_pre < 0) ” 
  &&  “ (INT_MIN < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ”
  &&  emp
|--
  “ ((-x_pre) = (Zabs (x_pre))) ”
  &&  emp
.

Definition gmp_abs_return_wit_2 := 
forall (x_pre: Z) ,
  “ (x_pre >= 0) ” 
  &&  “ (INT_MIN < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ”
  &&  emp
|--
  “ (x_pre = (Zabs (x_pre))) ”
  &&  emp
.

(*----- Function gmp_max -----*)

Definition gmp_max_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) ,
  “ (a_pre <= b_pre) ”
  &&  emp
|--
  “ (b_pre = (Z.max (a_pre) (b_pre))) ”
  &&  emp
.

Definition gmp_max_return_wit_2 := 
forall (b_pre: Z) (a_pre: Z) ,
  “ (a_pre > b_pre) ”
  &&  emp
|--
  “ (a_pre = (Z.max (a_pre) (b_pre))) ”
  &&  emp
.

(*----- Function gmp_cmp -----*)

Definition gmp_cmp_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) ,
  “ (a_pre >= b_pre) ” 
  &&  “ (a_pre > b_pre) ”
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((1 - 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (1 - 0 )) ”
.

Definition gmp_cmp_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) ,
  “ (a_pre < b_pre) ” 
  &&  “ (a_pre <= b_pre) ”
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((0 - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 - 1 )) ”
.

Definition gmp_cmp_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) ,
  “ (a_pre >= b_pre) ” 
  &&  “ (a_pre <= b_pre) ”
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((0 - 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 - 0 )) ”
.

Definition gmp_cmp_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) ,
  “ (a_pre < b_pre) ” 
  &&  “ (a_pre > b_pre) ”
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ False ”
.

Definition gmp_cmp_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) ,
  “ (a_pre >= b_pre) ” 
  &&  “ (a_pre > b_pre) ”
  &&  emp
|--
  (“ (a_pre < b_pre) ” 
  &&  “ ((1 - 0 ) = (-1)) ”
  &&  emp)
  ||
  (“ (a_pre = b_pre) ” 
  &&  “ ((1 - 0 ) = 0) ”
  &&  emp)
  ||
  (“ (a_pre > b_pre) ” 
  &&  “ ((1 - 0 ) = 1) ”
  &&  emp)
.

Definition gmp_cmp_return_wit_2 := 
forall (b_pre: Z) (a_pre: Z) ,
  “ (a_pre < b_pre) ” 
  &&  “ (a_pre <= b_pre) ”
  &&  emp
|--
  (“ (a_pre < b_pre) ” 
  &&  “ ((0 - 1 ) = (-1)) ”
  &&  emp)
  ||
  (“ (a_pre = b_pre) ” 
  &&  “ ((0 - 1 ) = 0) ”
  &&  emp)
  ||
  (“ (a_pre > b_pre) ” 
  &&  “ ((0 - 1 ) = 1) ”
  &&  emp)
.

Definition gmp_cmp_return_wit_3 := 
forall (b_pre: Z) (a_pre: Z) ,
  “ (a_pre >= b_pre) ” 
  &&  “ (a_pre <= b_pre) ”
  &&  emp
|--
  (“ (a_pre < b_pre) ” 
  &&  “ ((0 - 0 ) = (-1)) ”
  &&  emp)
  ||
  (“ (a_pre = b_pre) ” 
  &&  “ ((0 - 0 ) = 0) ”
  &&  emp)
  ||
  (“ (a_pre > b_pre) ” 
  &&  “ ((0 - 0 ) = 1) ”
  &&  emp)
.

(*----- Function mpn_copyi -----*)

Definition mpn_copyi_safety_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) (l: (@list Z)) ,
  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (UIntArray.full s_pre n_pre l )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (UIntArray.undef_full d_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_copyi_safety_wit_2 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) (l: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full d_pre (i + 1 ) (app ((sublist (0) (i) (l))) ((cons ((Znth i l 0)) (nil)))) )
  **  (UIntArray.undef_seg d_pre (i + 1 ) n_pre )
  **  (UIntArray.full s_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_copyi_entail_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) (l: (@list Z)) ,
  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full s_pre n_pre l )
  **  (UIntArray.undef_full d_pre n_pre )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full d_pre 0 (sublist (0) (0) (l)) )
  **  (UIntArray.undef_seg d_pre 0 n_pre )
  **  (UIntArray.full s_pre n_pre l )
.

Definition mpn_copyi_entail_wit_2 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) (l: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full d_pre (i + 1 ) (app ((sublist (0) (i) (l))) ((cons ((Znth i l 0)) (nil)))) )
  **  (UIntArray.undef_seg d_pre (i + 1 ) n_pre )
  **  (UIntArray.full s_pre n_pre l )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full d_pre (i + 1 ) (sublist (0) ((i + 1 )) (l)) )
  **  (UIntArray.undef_seg d_pre (i + 1 ) n_pre )
  **  (UIntArray.full s_pre n_pre l )
.

Definition mpn_copyi_return_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) (l: (@list Z)) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
  **  (UIntArray.undef_seg d_pre i n_pre )
  **  (UIntArray.full s_pre n_pre l )
|--
  (mpd_store_Z UINT_MOD s_pre val n_pre )
  **  (mpd_store_Z UINT_MOD d_pre val n_pre )
.

Definition mpn_copyi_partial_solve_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) ,
  (mpd_store_Z UINT_MOD s_pre val n_pre )
  **  (UIntArray.undef_full d_pre n_pre )
|--
  (mpd_store_Z UINT_MOD s_pre val n_pre )
  **  (UIntArray.undef_full d_pre n_pre )
.

Definition mpn_copyi_partial_solve_wit_2 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) (l: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
  **  (UIntArray.undef_seg d_pre i n_pre )
  **  (UIntArray.full s_pre n_pre l )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((s_pre + (i * sizeof(UINT) ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.missing_i s_pre i 0 n_pre l )
  **  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
  **  (UIntArray.undef_seg d_pre i n_pre )
.

Definition mpn_copyi_partial_solve_wit_3 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) (l: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full s_pre n_pre l )
  **  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
  **  (UIntArray.undef_seg d_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((d_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_seg d_pre (i + 1 ) n_pre )
  **  (UIntArray.full s_pre n_pre l )
  **  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
.

Definition mpn_copyi_which_implies_wit_1 := 
forall (val: Z) (n: Z) (s: Z) ,
  (mpd_store_Z UINT_MOD s val n )
|--
  EX (l: (@list Z)) ,
  “ ((Zlength (l)) = n) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full s n l )
.

(*----- Function mpn_cmp -----*)

Definition mpn_cmp_safety_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition mpn_cmp_safety_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  “ ((-1) <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_cmp_safety_wit_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  “ ((Znth n l1 0) > (Znth n l2 0)) ” 
  &&  “ ((Znth n l1 0) <> (Znth n l2 0)) ” 
  &&  “ (n >= 0) ” 
  &&  “ ((-1) <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_cmp_safety_wit_4 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  “ ((Znth n l1 0) <= (Znth n l2 0)) ” 
  &&  “ ((Znth n l1 0) <> (Znth n l2 0)) ” 
  &&  “ (n >= 0) ” 
  &&  “ ((-1) <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition mpn_cmp_safety_wit_5 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  “ ((Znth n l1 0) <= (Znth n l2 0)) ” 
  &&  “ ((Znth n l1 0) <> (Znth n l2 0)) ” 
  &&  “ (n >= 0) ” 
  &&  “ ((-1) <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_cmp_safety_wit_6 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  “ ((Znth n l1 0) = (Znth n l2 0)) ” 
  &&  “ (n >= 0) ” 
  &&  “ ((-1) <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition mpn_cmp_safety_wit_7 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  “ (n < 0) ” 
  &&  “ ((-1) <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_cmp_entail_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  “ ((-1) <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ ((sublist (((n_pre - 1 ) + 1 )) (n_pre) (l1)) = (sublist (((n_pre - 1 ) + 1 )) (n_pre) (l2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
.

Definition mpn_cmp_entail_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  “ ((Znth n l1 0) = (Znth n l2 0)) ” 
  &&  “ (n >= 0) ” 
  &&  “ ((-1) <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  “ ((-1) <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < n_pre) ” 
  &&  “ ((sublist (((n - 1 ) + 1 )) (n_pre) (l1)) = (sublist (((n - 1 ) + 1 )) (n_pre) (l2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
.

Definition mpn_cmp_return_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  “ (n < 0) ” 
  &&  “ ((-1) <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  (“ (val1 < val2) ” 
  &&  “ (0 = (-1)) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre ))
  ||
  (“ (val1 = val2) ” 
  &&  “ (0 = 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre ))
  ||
  (“ (val1 > val2) ” 
  &&  “ (0 = 1) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre ))
.

Definition mpn_cmp_return_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  “ ((Znth n l1 0) <= (Znth n l2 0)) ” 
  &&  “ ((Znth n l1 0) <> (Znth n l2 0)) ” 
  &&  “ (n >= 0) ” 
  &&  “ ((-1) <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  (“ (val1 < val2) ” 
  &&  “ ((-1) = (-1)) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre ))
  ||
  (“ (val1 = val2) ” 
  &&  “ ((-1) = 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre ))
  ||
  (“ (val1 > val2) ” 
  &&  “ ((-1) = 1) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre ))
.

Definition mpn_cmp_return_wit_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  “ ((Znth n l1 0) > (Znth n l2 0)) ” 
  &&  “ ((Znth n l1 0) <> (Znth n l2 0)) ” 
  &&  “ (n >= 0) ” 
  &&  “ ((-1) <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  (“ (val1 < val2) ” 
  &&  “ (1 = (-1)) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre ))
  ||
  (“ (val1 = val2) ” 
  &&  “ (1 = 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre ))
  ||
  (“ (val1 > val2) ” 
  &&  “ (1 = 1) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre ))
.

Definition mpn_cmp_partial_solve_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) ,
  “ (0 <= n_pre) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
|--
  “ (0 <= n_pre) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
.

Definition mpn_cmp_partial_solve_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  “ (n >= 0) ” 
  &&  “ ((-1) <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  “ (n >= 0) ” 
  &&  “ ((-1) <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (((ap_pre + (n * sizeof(UINT) ) )) # UInt  |-> (Znth n l1 0))
  **  (UIntArray.missing_i ap_pre n 0 n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
.

Definition mpn_cmp_partial_solve_wit_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  “ (n >= 0) ” 
  &&  “ ((-1) <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  “ (n >= 0) ” 
  &&  “ ((-1) <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (((bp_pre + (n * sizeof(UINT) ) )) # UInt  |-> (Znth n l2 0))
  **  (UIntArray.missing_i bp_pre n 0 n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
.

Definition mpn_cmp_partial_solve_wit_4 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  “ ((Znth n l1 0) <> (Znth n l2 0)) ” 
  &&  “ (n >= 0) ” 
  &&  “ ((-1) <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  “ ((Znth n l1 0) <> (Znth n l2 0)) ” 
  &&  “ (n >= 0) ” 
  &&  “ ((-1) <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (((ap_pre + (n * sizeof(UINT) ) )) # UInt  |-> (Znth n l1 0))
  **  (UIntArray.missing_i ap_pre n 0 n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
.

Definition mpn_cmp_partial_solve_wit_5 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  “ ((Znth n l1 0) <> (Znth n l2 0)) ” 
  &&  “ (n >= 0) ” 
  &&  “ ((-1) <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  “ ((Znth n l1 0) <> (Znth n l2 0)) ” 
  &&  “ (n >= 0) ” 
  &&  “ ((-1) <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (((bp_pre + (n * sizeof(UINT) ) )) # UInt  |-> (Znth n l2 0))
  **  (UIntArray.missing_i bp_pre n 0 n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
.

Definition mpn_cmp_which_implies_wit_1 := 
forall (val2: Z) (val1: Z) (n: Z) (ap: Z) (bp: Z) ,
  (mpd_store_Z_compact UINT_MOD ap val1 n )
  **  (mpd_store_Z_compact UINT_MOD bp val2 n )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ” 
  &&  “ ((last (l1) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l1 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ” 
  &&  “ ((last (l2) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD l2 ) ” 
  &&  “ (n = (Zlength (l1))) ” 
  &&  “ (n = (Zlength (l2))) ”
  &&  (UIntArray.full ap n l1 )
  **  (UIntArray.full bp n l2 )
.

(*----- Function mpn_cmp4 -----*)

Definition mpn_cmp4_safety_wit_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) ,
  “ (an_pre < bn_pre) ” 
  &&  “ (an_pre <> bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition mpn_cmp4_safety_wit_2 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) ,
  “ (an_pre < bn_pre) ” 
  &&  “ (an_pre <> bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_cmp4_safety_wit_3 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) ,
  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre <> bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_cmp4_return_wit_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (retval: Z) ,
  “ (val1 > val2) ” 
  &&  “ (retval = 1) ” 
  &&  “ (an_pre = bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  (“ (val1 < val2) ” 
  &&  “ (retval = (-1)) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
  ||
  (“ (val1 = val2) ” 
  &&  “ (retval = 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
  ||
  (“ (val1 > val2) ” 
  &&  “ (retval = 1) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
.

Definition mpn_cmp4_return_wit_2 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (retval: Z) ,
  “ (val1 = val2) ” 
  &&  “ (retval = 0) ” 
  &&  “ (an_pre = bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  (“ (val1 < val2) ” 
  &&  “ (retval = (-1)) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
  ||
  (“ (val1 = val2) ” 
  &&  “ (retval = 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
  ||
  (“ (val1 > val2) ” 
  &&  “ (retval = 1) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
.

Definition mpn_cmp4_return_wit_3 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (retval: Z) ,
  “ (val1 < val2) ” 
  &&  “ (retval = (-1)) ” 
  &&  “ (an_pre = bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  (“ (val1 < val2) ” 
  &&  “ (retval = (-1)) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
  ||
  (“ (val1 = val2) ” 
  &&  “ (retval = 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
  ||
  (“ (val1 > val2) ” 
  &&  “ (retval = 1) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
.

Definition mpn_cmp4_return_wit_4 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) ,
  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre <> bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  (“ (val1 < val2) ” 
  &&  “ (1 = (-1)) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
  ||
  (“ (val1 = val2) ” 
  &&  “ (1 = 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
  ||
  (“ (val1 > val2) ” 
  &&  “ (1 = 1) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
.

Definition mpn_cmp4_return_wit_5 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) ,
  “ (an_pre < bn_pre) ” 
  &&  “ (an_pre <> bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  (“ (val1 < val2) ” 
  &&  “ ((-1) = (-1)) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
  ||
  (“ (val1 = val2) ” 
  &&  “ ((-1) = 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
  ||
  (“ (val1 > val2) ” 
  &&  “ ((-1) = 1) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
.

Definition mpn_cmp4_partial_solve_wit_1_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) ,
  “ (an_pre = bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  “ (0 <= an_pre) ”
.

Definition mpn_cmp4_partial_solve_wit_1_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) ,
  “ (an_pre = bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  “ (0 <= an_pre) ” 
  &&  “ (an_pre = bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
.

Definition mpn_cmp4_partial_solve_wit_1 := mpn_cmp4_partial_solve_wit_1_pure -> mpn_cmp4_partial_solve_wit_1_aux.

(*----- Function mpn_normalized_size -----*)

Definition mpn_normalized_size_safety_wit_1 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) ,
  “ (n >= 0) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_normalized_size_safety_wit_2 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) ,
  “ (n > 0) ” 
  &&  “ (n >= 0) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition mpn_normalized_size_safety_wit_3 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) ,
  “ (n > 0) ” 
  &&  “ (n >= 0) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_normalized_size_safety_wit_4 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) ,
  “ (n > 0) ” 
  &&  “ (n >= 0) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.undef_seg xp_pre n n_pre )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_normalized_size_safety_wit_5 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) ,
  “ ((Znth (n - 1 ) (sublist (0) (n) (l)) 0) = 0) ” 
  &&  “ (n > 0) ” 
  &&  “ (n >= 0) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.undef_seg xp_pre n n_pre )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition mpn_normalized_size_entail_wit_1 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) ,
  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
  **  (UIntArray.full xp_pre n_pre l )
|--
  “ (n_pre <= INT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
  **  (UIntArray.full xp_pre n_pre l )
.

Definition mpn_normalized_size_entail_wit_2 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) ,
  “ (n_pre <= INT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full xp_pre n_pre l )
|--
  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n_pre) (l)))) = val) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full xp_pre n_pre (sublist (0) (n_pre) (l)) )
  **  (UIntArray.undef_seg xp_pre n_pre n_pre )
.

Definition mpn_normalized_size_entail_wit_3 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) ,
  “ ((Znth (n - 1 ) (sublist (0) (n) (l)) 0) = 0) ” 
  &&  “ (n > 0) ” 
  &&  “ (n >= 0) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
|--
  “ ((n - 1 ) >= 0) ” 
  &&  “ ((n - 1 ) <= n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((n - 1 )) (l)))) = val) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full xp_pre (n - 1 ) (sublist (0) ((n - 1 )) (l)) )
  **  (UIntArray.undef_seg xp_pre (n - 1 ) n_pre )
.

Definition mpn_normalized_size_return_wit_1 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) ,
  “ (n <= 0) ” 
  &&  “ (n >= 0) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
|--
  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ”
  &&  (mpd_store_Z_compact UINT_MOD xp_pre val n )
  **  (UIntArray.undef_seg xp_pre n n_pre )
.

Definition mpn_normalized_size_return_wit_2 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) ,
  “ ((Znth (n - 1 ) (sublist (0) (n) (l)) 0) <> 0) ” 
  &&  “ (n > 0) ” 
  &&  “ (n >= 0) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
|--
  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ”
  &&  (mpd_store_Z_compact UINT_MOD xp_pre val n )
  **  (UIntArray.undef_seg xp_pre n n_pre )
.

Definition mpn_normalized_size_partial_solve_wit_1 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) ,
  “ (0 <= n_pre) ”
  &&  (mpd_store_Z UINT_MOD xp_pre val n_pre )
|--
  “ (0 <= n_pre) ”
  &&  (mpd_store_Z UINT_MOD xp_pre val n_pre )
.

Definition mpn_normalized_size_partial_solve_wit_2 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) ,
  “ (n > 0) ” 
  &&  “ (n >= 0) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
|--
  “ (n > 0) ” 
  &&  “ (n >= 0) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ”
  &&  (((xp_pre + ((n - 1 ) * sizeof(UINT) ) )) # UInt  |-> (Znth (n - 1 ) (sublist (0) (n) (l)) 0))
  **  (UIntArray.missing_i xp_pre (n - 1 ) 0 n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
.

Definition mpn_normalized_size_which_implies_wit_1 := 
forall (val: Z) (n: Z) (xp: Z) ,
  (mpd_store_Z UINT_MOD xp val n )
|--
  EX (l: (@list Z)) ,
  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n) ”
  &&  (UIntArray.full xp n l )
.

(*----- Function mpn_add_1 -----*)

Definition mpn_add_1_safety_wit_1 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "b" ) )) # UInt  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_add_1_safety_wit_2 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  “ ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) >= b_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (((rp_pre + (0 * sizeof(UINT) ) )) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)))
  **  (UIntArray.undef_missing_i rp_pre 0 0 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)))
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "b" ) )) # UInt  |-> 0)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ ((0 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 + 1 )) ”
.

Definition mpn_add_1_safety_wit_3 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  “ ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) < b_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (((rp_pre + (0 * sizeof(UINT) ) )) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)))
  **  (UIntArray.undef_missing_i rp_pre 0 0 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)))
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "b" ) )) # UInt  |-> 1)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ ((0 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 + 1 )) ”
.

Definition mpn_add_1_safety_wit_4 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l': (@list Z)) (val1: Z) (val2: Z) (b: Z) (i: Z) ,
  “ ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b < UINT_MOD) ” 
  &&  “ ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) ” 
  &&  “ ((Zlength (l')) = i) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full rp_pre (i + 1 ) (app (l') ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth i l 0) + b )) (32)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "b" ) )) # UInt  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_1_safety_wit_5 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l': (@list Z)) (val1: Z) (val2: Z) (b: Z) (i: Z) ,
  “ ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b < UINT_MOD) ” 
  &&  “ ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) ” 
  &&  “ ((Zlength (l')) = i) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full rp_pre (i + 1 ) (app (l') ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth i l 0) + b )) (32)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "b" ) )) # UInt  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_1_entail_wit_1_1 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l'_2: (@list Z)) (val1_2: Z) (val2_2: Z) (b: Z) (i: Z) ,
  “ ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b < UINT_MOD) ” 
  &&  “ ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b_pre )) ” 
  &&  “ ((Zlength (l'_2)) = i) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l'_2)) = val2_2) ” 
  &&  “ (list_within_bound UINT_MOD l'_2 ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full rp_pre (i + 1 ) (app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
|--
  EX (l': (@list Z))  (val1: Z)  (val2: Z) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 < UINT_MOD) ” 
  &&  “ ((val2 + (1 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val1 + b_pre )) ” 
  &&  “ ((Zlength (l')) = (i + 1 )) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre (i + 1 ) l' )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
.

Definition mpn_add_1_entail_wit_1_2 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l'_2: (@list Z)) (val1_2: Z) (val2_2: Z) (b: Z) (i: Z) ,
  “ ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b < UINT_MOD) ” 
  &&  “ ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b_pre )) ” 
  &&  “ ((Zlength (l'_2)) = i) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l'_2)) = val2_2) ” 
  &&  “ (list_within_bound UINT_MOD l'_2 ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full rp_pre (i + 1 ) (app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
|--
  EX (l': (@list Z))  (val1: Z)  (val2: Z) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < UINT_MOD) ” 
  &&  “ ((val2 + (0 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val1 + b_pre )) ” 
  &&  “ ((Zlength (l')) = (i + 1 )) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre (i + 1 ) l' )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
.

Definition mpn_add_1_entail_wit_2_1 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  “ ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) < b_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (((rp_pre + (0 * sizeof(UINT) ) )) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)))
  **  (UIntArray.undef_missing_i rp_pre 0 0 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
|--
  EX (l': (@list Z))  (val1: Z)  (val2: Z) ,
  “ (1 <= (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 < UINT_MOD) ” 
  &&  “ ((val2 + (1 * (Z.pow (UINT_MOD) ((0 + 1 ))) ) ) = (val1 + b_pre )) ” 
  &&  “ ((Zlength (l')) = (0 + 1 )) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((0 + 1 )) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre (0 + 1 ) l' )
  **  (UIntArray.undef_seg rp_pre (0 + 1 ) n_pre )
.

Definition mpn_add_1_entail_wit_2_2 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  “ ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) >= b_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (((rp_pre + (0 * sizeof(UINT) ) )) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)))
  **  (UIntArray.undef_missing_i rp_pre 0 0 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
|--
  EX (l': (@list Z))  (val1: Z)  (val2: Z) ,
  “ (1 <= (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < UINT_MOD) ” 
  &&  “ ((val2 + (0 * (Z.pow (UINT_MOD) ((0 + 1 ))) ) ) = (val1 + b_pre )) ” 
  &&  “ ((Zlength (l')) = (0 + 1 )) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((0 + 1 )) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre (0 + 1 ) l' )
  **  (UIntArray.undef_seg rp_pre (0 + 1 ) n_pre )
.

Definition mpn_add_1_return_wit_1 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l': (@list Z)) (val1: Z) (val2: Z) (b: Z) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b < UINT_MOD) ” 
  &&  “ ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) ” 
  &&  “ ((Zlength (l')) = i) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre i l' )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  EX (val': Z) ,
  “ ((val' + (b * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val + b_pre )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val n_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val' n_pre )
.

Definition mpn_add_1_partial_solve_wit_1 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) ,
  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val n_pre )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val n_pre )
  **  (UIntArray.undef_full rp_pre n_pre )
.

Definition mpn_add_1_partial_solve_wit_2 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (((ap_pre + (0 * sizeof(UINT) ) )) # UInt  |-> (Znth 0 l 0))
  **  (UIntArray.missing_i ap_pre 0 0 n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
.

Definition mpn_add_1_partial_solve_wit_3 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  “ ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) < b_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) < b_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (((rp_pre + (0 * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_missing_i rp_pre 0 0 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
.

Definition mpn_add_1_partial_solve_wit_4 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  “ ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) >= b_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) >= b_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (((rp_pre + (0 * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_missing_i rp_pre 0 0 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
.

Definition mpn_add_1_partial_solve_wit_5 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l': (@list Z)) (val1: Z) (val2: Z) (b: Z) (i: Z) ,
  “ ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b < UINT_MOD) ” 
  &&  “ ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) ” 
  &&  “ ((Zlength (l')) = i) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre i l' )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b < UINT_MOD) ” 
  &&  “ ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) ” 
  &&  “ ((Zlength (l')) = i) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre i l' )
.

Definition mpn_add_1_partial_solve_wit_6 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l': (@list Z)) (val1: Z) (val2: Z) (b: Z) (i: Z) ,
  “ ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b < UINT_MOD) ” 
  &&  “ ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) ” 
  &&  “ ((Zlength (l')) = i) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre i l' )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b < UINT_MOD) ” 
  &&  “ ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) ” 
  &&  “ ((Zlength (l')) = i) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre i l' )
.

Definition mpn_add_1_partial_solve_wit_7 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l': (@list Z)) (val1: Z) (val2: Z) (b: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b < UINT_MOD) ” 
  &&  “ ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) ” 
  &&  “ ((Zlength (l')) = i) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre i l' )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b < UINT_MOD) ” 
  &&  “ ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) ” 
  &&  “ ((Zlength (l')) = i) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((ap_pre + (i * sizeof(UINT) ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.missing_i ap_pre i 0 n_pre l )
  **  (UIntArray.full rp_pre i l' )
  **  (UIntArray.undef_seg rp_pre i n_pre )
.

Definition mpn_add_1_which_implies_wit_1 := 
forall (val: Z) (n: Z) (ap: Z) ,
  (mpd_store_Z UINT_MOD ap val n )
|--
  EX (l: (@list Z)) ,
  “ ((Zlength (l)) = n) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full ap n l )
.

(*----- Function mpn_add_n -----*)

Definition mpn_add_n_safety_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_b: (@list Z)) (l_a: (@list Z)) ,
  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_add_n_safety_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_b: (@list Z)) (l_a: (@list Z)) ,
  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_add_n_safety_wit_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full rp_pre (i + 1 ) (app (l_r) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> (0 + 0 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_n_safety_wit_4 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full rp_pre (i + 1 ) (app (l_r) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> (0 + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_n_safety_wit_5 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full rp_pre (i + 1 ) (app (l_r) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> (1 + 0 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_n_safety_wit_6 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full rp_pre (i + 1 ) (app (l_r) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> (1 + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_n_entail_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) ,
  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = 0) ” 
  &&  “ ((val_r + (0 * (Z.pow (UINT_MOD) (0)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full rp_pre 0 l_r )
  **  (UIntArray.undef_seg rp_pre 0 n_pre )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
.

Definition mpn_add_n_entail_wit_2_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2) ” 
  &&  “ (list_within_bound UINT_MOD l_r_2 ) ” 
  &&  “ ((Zlength (l_r_2)) = i) ” 
  &&  “ ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full rp_pre (i + 1 ) (app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (1 + 1 )) ” 
  &&  “ ((1 + 1 ) <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((val_r + ((1 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full rp_pre (i + 1 ) l_r )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
.

Definition mpn_add_n_entail_wit_2_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2) ” 
  &&  “ (list_within_bound UINT_MOD l_r_2 ) ” 
  &&  “ ((Zlength (l_r_2)) = i) ” 
  &&  “ ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full rp_pre (i + 1 ) (app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (1 + 0 )) ” 
  &&  “ ((1 + 0 ) <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((val_r + ((1 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full rp_pre (i + 1 ) l_r )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
.

Definition mpn_add_n_entail_wit_2_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2) ” 
  &&  “ (list_within_bound UINT_MOD l_r_2 ) ” 
  &&  “ ((Zlength (l_r_2)) = i) ” 
  &&  “ ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full rp_pre (i + 1 ) (app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((val_r + ((0 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full rp_pre (i + 1 ) l_r )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
.

Definition mpn_add_n_entail_wit_2_4 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2) ” 
  &&  “ (list_within_bound UINT_MOD l_r_2 ) ” 
  &&  “ ((Zlength (l_r_2)) = i) ” 
  &&  “ ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full rp_pre (i + 1 ) (app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (0 + 0 )) ” 
  &&  “ ((0 + 0 ) <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((val_r + ((0 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full rp_pre (i + 1 ) l_r )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
.

Definition mpn_add_n_return_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_seg rp_pre i n_pre )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
|--
  EX (val_r_out: Z) ,
  “ ((val_r_out + (cy * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val_a + val_b )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a n_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b n_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out n_pre )
.

Definition mpn_add_n_partial_solve_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) ,
  “ (n_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a n_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b n_pre )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (n_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a n_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b n_pre )
  **  (UIntArray.undef_full rp_pre n_pre )
.

Definition mpn_add_n_partial_solve_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_seg rp_pre i n_pre )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((ap_pre + (i * sizeof(UINT) ) )) # UInt  |-> (Znth i l_a 0))
  **  (UIntArray.missing_i ap_pre i 0 n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_seg rp_pre i n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
.

Definition mpn_add_n_partial_solve_wit_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_seg rp_pre i n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((bp_pre + (i * sizeof(UINT) ) )) # UInt  |-> (Znth i l_b 0))
  **  (UIntArray.missing_i bp_pre i 0 n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_seg rp_pre i n_pre )
.

Definition mpn_add_n_partial_solve_wit_4 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
.

Definition mpn_add_n_partial_solve_wit_5 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
.

Definition mpn_add_n_partial_solve_wit_6 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
.

Definition mpn_add_n_partial_solve_wit_7 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
.

Definition mpn_add_n_which_implies_wit_1 := 
forall (val_b: Z) (val_a: Z) (n: Z) (ap: Z) (bp: Z) ,
  (mpd_store_Z UINT_MOD ap val_a n )
  **  (mpd_store_Z UINT_MOD bp val_b n )
|--
  EX (l_b: (@list Z))  (l_a: (@list Z)) ,
  “ ((Zlength (l_a)) = n) ” 
  &&  “ ((Zlength (l_b)) = n) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ”
  &&  (UIntArray.full ap n l_a )
  **  (UIntArray.full bp n l_b )
.

(*----- Function mpn_add -----*)

Definition mpn_add_safety_wit_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out: Z) (retval: Z) (l_r: (@list Z)) ,
  “ (an_pre > bn_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ ((Zlength (l_r)) = bn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r_out) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b )) ” 
  &&  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  “ ((an_pre - bn_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (an_pre - bn_pre )) ”
.

Definition mpn_add_entail_wit_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out: Z) (retval: Z) (l_r: (@list Z)) ,
  “ ((Zlength (l_r)) = bn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r_out) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b )) ” 
  &&  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ ((Zlength (l_r)) = bn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r_out) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b )) ” 
  &&  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
.

Definition mpn_add_return_wit_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out_2: Z) (retval_2: Z) (l_r: (@list Z)) (val': Z) (retval: Z) ,
  “ ((val' + (retval * (Z.pow (UINT_MOD) ((an_pre - bn_pre ))) ) ) = (val_a_high + retval_2 )) ” 
  &&  “ (an_pre > bn_pre) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= UINT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ ((Zlength (l_r)) = bn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r_out_2) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((val_r_out_2 + (retval_2 * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b )) ” 
  &&  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (rp_pre + (bn_pre * sizeof(UINT) ) ) val' (an_pre - bn_pre ) )
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
|--
  EX (val_r_out: Z) ,
  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a + val_b )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out an_pre )
.

Definition mpn_add_return_wit_2 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out_2: Z) (retval: Z) (l_r: (@list Z)) ,
  “ (an_pre <= bn_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ ((Zlength (l_r)) = bn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r_out_2) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((val_r_out_2 + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b )) ” 
  &&  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
|--
  EX (val_r_out: Z) ,
  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a + val_b )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out an_pre )
.

Definition mpn_add_partial_solve_wit_1_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) ,
  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
|--
  “ (an_pre >= bn_pre) ” 
  &&  “ (bn_pre >= 0) ”
.

Definition mpn_add_partial_solve_wit_1_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) ,
  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
|--
  “ (an_pre >= bn_pre) ” 
  &&  “ (bn_pre >= 0) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
.

Definition mpn_add_partial_solve_wit_1 := mpn_add_partial_solve_wit_1_pure -> mpn_add_partial_solve_wit_1_aux.

Definition mpn_add_partial_solve_wit_2_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) ,
  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
|--
  “ (an_pre >= bn_pre) ” 
  &&  “ (bn_pre >= 0) ”
.

Definition mpn_add_partial_solve_wit_2_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) ,
  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
|--
  “ (an_pre >= bn_pre) ” 
  &&  “ (bn_pre >= 0) ” 
  &&  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (UIntArray.undef_full rp_pre an_pre )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
.

Definition mpn_add_partial_solve_wit_2 := mpn_add_partial_solve_wit_2_pure -> mpn_add_partial_solve_wit_2_aux.

Definition mpn_add_partial_solve_wit_3_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) ,
  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.undef_full rp_pre bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
|--
  “ (bn_pre >= 0) ”
.

Definition mpn_add_partial_solve_wit_3_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) ,
  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (UIntArray.undef_full rp_pre bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
|--
  “ (bn_pre >= 0) ” 
  &&  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
.

Definition mpn_add_partial_solve_wit_3 := mpn_add_partial_solve_wit_3_pure -> mpn_add_partial_solve_wit_3_aux.

Definition mpn_add_partial_solve_wit_4 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out: Z) (retval: Z) ,
  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b )) ” 
  &&  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
|--
  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b )) ” 
  &&  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD rp_pre val_r_out bn_pre )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
.

Definition mpn_add_partial_solve_wit_5_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out: Z) (retval: Z) (l_r: (@list Z)) ,
  “ (an_pre > bn_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ ((Zlength (l_r)) = bn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r_out) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b )) ” 
  &&  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ”
.

Definition mpn_add_partial_solve_wit_5_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out: Z) (retval: Z) (l_r: (@list Z)) ,
  “ (an_pre > bn_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ ((Zlength (l_r)) = bn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r_out) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b )) ” 
  &&  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
|--
  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre > bn_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ ((Zlength (l_r)) = bn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r_out) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b )) ” 
  &&  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
.

Definition mpn_add_partial_solve_wit_5 := mpn_add_partial_solve_wit_5_pure -> mpn_add_partial_solve_wit_5_aux.

Definition mpn_add_which_implies_wit_1 := 
forall (val_a: Z) (an: Z) (ap: Z) (bn: Z) ,
  “ (an >= bn) ” 
  &&  “ (bn >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap val_a an )
|--
  EX (val_a_high: Z)  (val_a_low: Z) ,
  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn)) ) )) ”
  &&  (mpd_store_Z UINT_MOD ap val_a_low bn )
  **  (mpd_store_Z UINT_MOD (ap + (bn * sizeof(UINT) ) ) val_a_high (an - bn ) )
.

Definition mpn_add_which_implies_wit_2 := 
forall (an: Z) (bn: Z) (rp: Z) ,
  “ (an >= bn) ” 
  &&  “ (bn >= 0) ”
  &&  (UIntArray.undef_full rp an )
|--
  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_full (rp + (bn * sizeof(UINT) ) ) (an - bn ) )
.

Definition mpn_add_which_implies_wit_3 := 
forall (val_r_out: Z) (bn: Z) (rp: Z) ,
  (mpd_store_Z UINT_MOD rp val_r_out bn )
|--
  EX (l_r: (@list Z)) ,
  “ ((Zlength (l_r)) = bn) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r_out) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ”
  &&  (UIntArray.full rp bn l_r )
.

(*----- Function gmp_umul_ppmm -----*)

Definition gmp_umul_ppmm_safety_wit_1 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |->_)
  **  ((( &( "__uh" ) )) # UInt  |->_)
  **  ((( &( "__vl" ) )) # UInt  |->_)
  **  ((( &( "__ul" ) )) # UInt  |->_)
  **  ((( &( "__x3" ) )) # UInt  |->_)
  **  ((( &( "__x2" ) )) # UInt  |->_)
  **  ((( &( "__x1" ) )) # UInt  |->_)
  **  ((( &( "__x0" ) )) # UInt  |->_)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (65535 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65535) ”
.

Definition gmp_umul_ppmm_safety_wit_2 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |->_)
  **  ((( &( "__uh" ) )) # UInt  |->_)
  **  ((( &( "__vl" ) )) # UInt  |->_)
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |->_)
  **  ((( &( "__x2" ) )) # UInt  |->_)
  **  ((( &( "__x1" ) )) # UInt  |->_)
  **  ((( &( "__x0" ) )) # UInt  |->_)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= 31) ” 
  &&  “ (0 <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_3 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |->_)
  **  ((( &( "__uh" ) )) # UInt  |->_)
  **  ((( &( "__vl" ) )) # UInt  |->_)
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |->_)
  **  ((( &( "__x2" ) )) # UInt  |->_)
  **  ((( &( "__x1" ) )) # UInt  |->_)
  **  ((( &( "__x0" ) )) # UInt  |->_)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_4 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |->_)
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |->_)
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |->_)
  **  ((( &( "__x2" ) )) # UInt  |->_)
  **  ((( &( "__x1" ) )) # UInt  |->_)
  **  ((( &( "__x0" ) )) # UInt  |->_)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (65535 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65535) ”
.

Definition gmp_umul_ppmm_safety_wit_5 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |->_)
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |->_)
  **  ((( &( "__x2" ) )) # UInt  |->_)
  **  ((( &( "__x1" ) )) # UInt  |->_)
  **  ((( &( "__x0" ) )) # UInt  |->_)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= 31) ” 
  &&  “ (0 <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_6 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |->_)
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |->_)
  **  ((( &( "__x2" ) )) # UInt  |->_)
  **  ((( &( "__x1" ) )) # UInt  |->_)
  **  ((( &( "__x0" ) )) # UInt  |->_)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_7 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= 31) ” 
  &&  “ (0 <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_8 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_9 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32))) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (65536 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65536) ”
.

Definition gmp_umul_ppmm_safety_wit_10 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) >= (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32))) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= 31) ” 
  &&  “ (0 <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_11 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) >= (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32))) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_12 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32))) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= 31) ” 
  &&  “ (0 <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_13 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32))) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_14 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32))) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  “ (16 <= 31) ” 
  &&  “ (0 <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_15 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32))) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_16 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32))) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  “ (65535 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65535) ”
.

Definition gmp_umul_ppmm_safety_wit_17 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) >= (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32))) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  “ (16 <= 31) ” 
  &&  “ (0 <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_18 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) >= (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32))) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_19 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) >= (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32))) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  “ (65535 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65535) ”
.

Definition gmp_umul_ppmm_entail_wit_1 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |->_)
  **  ((( &( "__uh" ) )) # UInt  |->_)
  **  ((( &( "__vl" ) )) # UInt  |->_)
  **  ((( &( "__ul" ) )) # UInt  |->_)
  **  ((( &( "__x3" ) )) # UInt  |->_)
  **  ((( &( "__x2" ) )) # UInt  |->_)
  **  ((( &( "__x1" ) )) # UInt  |->_)
  **  ((( &( "__x0" ) )) # UInt  |->_)
  **  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |->_)
  **  ((( &( "__uh" ) )) # UInt  |->_)
  **  ((( &( "__vl" ) )) # UInt  |->_)
  **  ((( &( "__ul" ) )) # UInt  |->_)
  **  ((( &( "__x3" ) )) # UInt  |->_)
  **  ((( &( "__x2" ) )) # UInt  |->_)
  **  ((( &( "__x1" ) )) # UInt  |->_)
  **  ((( &( "__x0" ) )) # UInt  |->_)
  **  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
.

Definition gmp_umul_ppmm_entail_wit_2 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |->_)
  **  ((( &( "__uh" ) )) # UInt  |->_)
  **  ((( &( "__vl" ) )) # UInt  |->_)
  **  ((( &( "__ul" ) )) # UInt  |->_)
  **  ((( &( "__x3" ) )) # UInt  |->_)
  **  ((( &( "__x2" ) )) # UInt  |->_)
  **  ((( &( "__x1" ) )) # UInt  |->_)
  **  ((( &( "__x0" ) )) # UInt  |->_)
  **  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |->_)
  **  ((( &( "__uh" ) )) # UInt  |->_)
  **  ((( &( "__vl" ) )) # UInt  |->_)
  **  ((( &( "__ul" ) )) # UInt  |->_)
  **  ((( &( "__x3" ) )) # UInt  |->_)
  **  ((( &( "__x2" ) )) # UInt  |->_)
  **  ((( &( "__x1" ) )) # UInt  |->_)
  **  ((( &( "__x0" ) )) # UInt  |->_)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
.

Definition gmp_umul_ppmm_return_wit_1 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32))) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((w0_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16)) (32)) + (Z.land ((Z.land u_pre 65535) * (Z.land v_pre 65535) ) 65535) )) (32)))
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  EX (w0_value: Z)  (w1_value: Z) ,
  “ (((w1_value * UINT_MOD ) + w0_value ) = (u_pre * v_pre )) ”
  &&  ((w0_pre) # UInt  |-> w0_value)
  **  ((w1_pre) # UInt  |-> w1_value)
.

Definition gmp_umul_ppmm_return_wit_2 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) >= (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32))) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (u_pre >= 0) ” 
  &&  “ (v_pre >= 0) ”
  &&  ((w0_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16)) (32)) + (Z.land ((Z.land u_pre 65535) * (Z.land v_pre 65535) ) 65535) )) (32)))
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  EX (w0_value: Z)  (w1_value: Z) ,
  “ (((w1_value * UINT_MOD ) + w0_value ) = (u_pre * v_pre )) ”
  &&  ((w0_pre) # UInt  |-> w0_value)
  **  ((w1_pre) # UInt  |-> w1_value)
.

(*----- Function mpn_mul_1 -----*)

Definition mpn_mul_1_safety_wit_1 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) ,
  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "lpl" ) )) # UInt  |->_)
  **  ((( &( "hpl" ) )) # UInt  |->_)
  **  ((( &( "cl" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_mul_1_safety_wit_2 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) ,
  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "lpl" ) )) # UInt  |->_)
  **  ((( &( "hpl" ) )) # UInt  |->_)
  **  ((( &( "cl" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_mul_1_safety_wit_3 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) ,
  “ ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ (0 <= lpl) ” 
  &&  “ (lpl <= UINT_MAX) ” 
  &&  “ (0 <= hpl) ” 
  &&  “ (hpl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) (app (l_rp) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> (0 + hpl ))
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits ((lpl + cl )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.full up_pre n_pre l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_mul_1_safety_wit_4 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) ,
  “ ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ (0 <= lpl) ” 
  &&  “ (lpl <= UINT_MAX) ” 
  &&  “ (0 <= hpl) ” 
  &&  “ (hpl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) (app (l_rp) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> (0 + hpl ))
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits ((lpl + cl )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.full up_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_mul_1_safety_wit_5 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) ,
  “ ((unsigned_last_nbits ((lpl + cl )) (32)) < cl) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ (0 <= lpl) ” 
  &&  “ (lpl <= UINT_MAX) ” 
  &&  “ (0 <= hpl) ” 
  &&  “ (hpl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) (app (l_rp) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> (unsigned_last_nbits ((1 + hpl )) (32)))
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits ((lpl + cl )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.full up_pre n_pre l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_mul_1_safety_wit_6 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) ,
  “ ((unsigned_last_nbits ((lpl + cl )) (32)) < cl) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ (0 <= lpl) ” 
  &&  “ (lpl <= UINT_MAX) ” 
  &&  “ (0 <= hpl) ” 
  &&  “ (hpl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) (app (l_rp) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> (unsigned_last_nbits ((1 + hpl )) (32)))
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits ((lpl + cl )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.full up_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_mul_1_entail_wit_1 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) ,
  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  EX (l_rp: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = 0) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (0 * (Z.pow (UINT_MOD) (0)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l)))) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 0 l_rp )
  **  (UIntArray.undef_seg rp_pre 0 n_pre )
.

Definition mpn_mul_1_entail_wit_2 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp: (@list Z)) (cl: Z) (i: Z) (w0_value: Z) (w1_value: Z) ,
  “ (((w1_value * UINT_MOD ) + w0_value ) = ((Znth i l 0) * vl_pre )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  ((( &( "lpl" ) )) # UInt  |-> w0_value)
  **  ((( &( "hpl" ) )) # UInt  |-> w1_value)
  **  (UIntArray.full up_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> cl)
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ ((Znth i l 0) <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (vl_pre >= 0) ” 
  &&  “ ((Znth i l 0) >= 0) ” 
  &&  “ (cl >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = ((Znth i l 0) * vl_pre )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  ((( &( "lpl" ) )) # UInt  |-> w0_value)
  **  ((( &( "hpl" ) )) # UInt  |-> w1_value)
  **  (UIntArray.full up_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> cl)
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
.

Definition mpn_mul_1_entail_wit_3 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp: (@list Z)) (cl: Z) (i: Z) (w0_value: Z) (w1_value: Z) ,
  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ ((Znth i l 0) <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (vl_pre >= 0) ” 
  &&  “ ((Znth i l 0) >= 0) ” 
  &&  “ (cl >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = ((Znth i l 0) * vl_pre )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  ((( &( "lpl" ) )) # UInt  |-> w0_value)
  **  ((( &( "hpl" ) )) # UInt  |-> w1_value)
  **  (UIntArray.full up_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> cl)
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ (0 <= w1_value) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (w0_value >= 0) ” 
  &&  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ ((Znth i l 0) <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (vl_pre >= 0) ” 
  &&  “ ((Znth i l 0) >= 0) ” 
  &&  “ (cl >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = ((Znth i l 0) * vl_pre )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  ((( &( "hpl" ) )) # UInt  |-> w1_value)
  **  ((( &( "lpl" ) )) # UInt  |-> w0_value)
  **  (UIntArray.full up_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> cl)
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
.

Definition mpn_mul_1_entail_wit_4 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp_2: (@list Z)) (cl: Z) (i: Z) (w0_value: Z) (w1_value: Z) ,
  “ (0 <= w1_value) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (w0_value >= 0) ” 
  &&  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ ((Znth i l 0) <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (vl_pre >= 0) ” 
  &&  “ ((Znth i l 0) >= 0) ” 
  &&  “ (cl >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = ((Znth i l 0) * vl_pre )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp_2)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp_2 ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp_2)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp_2 )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  EX (l_rp: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ (0 <= w1_value) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = ((Znth i l 0) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
.

Definition mpn_mul_1_entail_wit_5_1 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) ,
  “ ((unsigned_last_nbits ((lpl + cl )) (32)) < cl) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ (0 <= lpl) ” 
  &&  “ (lpl <= UINT_MAX) ” 
  &&  “ (0 <= hpl) ” 
  &&  “ (hpl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp_2)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp_2 ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp_2)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) (app (l_rp_2) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits ((lpl + cl )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.full up_pre n_pre l )
|--
  EX (l_rp: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (unsigned_last_nbits ((1 + hpl )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((1 + hpl )) (32)) <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + ((unsigned_last_nbits ((1 + hpl )) (32)) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 (i + 1 ) l_rp )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  ((( &( "lpl" ) )) # UInt  |->_)
  **  ((( &( "hpl" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
.

Definition mpn_mul_1_entail_wit_5_2 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) ,
  “ ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ (0 <= lpl) ” 
  &&  “ (lpl <= UINT_MAX) ” 
  &&  “ (0 <= hpl) ” 
  &&  “ (hpl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp_2)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp_2 ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp_2)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) (app (l_rp_2) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits ((lpl + cl )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.full up_pre n_pre l )
|--
  EX (l_rp: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (0 + hpl )) ” 
  &&  “ ((0 + hpl ) <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + ((0 + hpl ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 (i + 1 ) l_rp )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  ((( &( "lpl" ) )) # UInt  |->_)
  **  ((( &( "hpl" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
.

Definition mpn_mul_1_return_wit_1 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp: (@list Z)) (cl: Z) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  EX (val': Z)  (l': (@list Z)) ,
  “ ((Zlength (l')) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val') ” 
  &&  “ ((val' + (cl * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l)) * vl_pre )) ”
  &&  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.full rp_pre n_pre l' )
.

Definition mpn_mul_1_partial_solve_wit_1 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp: (@list Z)) (cl: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((up_pre + (i * sizeof(UINT) ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.missing_i up_pre i 0 n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
.

Definition mpn_mul_1_partial_solve_wit_2 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp: (@list Z)) (cl: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
.

Definition mpn_mul_1_partial_solve_wit_3 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) ,
  “ ((unsigned_last_nbits ((lpl + cl )) (32)) < cl) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ (0 <= lpl) ” 
  &&  “ (lpl <= UINT_MAX) ” 
  &&  “ (0 <= hpl) ” 
  &&  “ (hpl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((unsigned_last_nbits ((lpl + cl )) (32)) < cl) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ (0 <= lpl) ” 
  &&  “ (lpl <= UINT_MAX) ” 
  &&  “ (0 <= hpl) ” 
  &&  “ (hpl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
.

Definition mpn_mul_1_partial_solve_wit_4 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) ,
  “ ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ (0 <= lpl) ” 
  &&  “ (lpl <= UINT_MAX) ” 
  &&  “ (0 <= hpl) ” 
  &&  “ (hpl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ (0 <= lpl) ” 
  &&  “ (lpl <= UINT_MAX) ” 
  &&  “ (0 <= hpl) ” 
  &&  “ (hpl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
.

(*----- Function mpn_sub_1 -----*)

Definition mpn_sub_1_safety_wit_1 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "b" ) )) # UInt  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_sub_1_safety_wit_2 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  “ ((Znth 0 l 0) < b_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (((rp_pre + (0 * sizeof(UINT) ) )) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) - b_pre )) (32)))
  **  (UIntArray.undef_missing_i rp_pre 0 0 n_pre )
  **  ((( &( "cy" ) )) # UInt  |-> 1)
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "a" ) )) # UInt  |-> (Znth 0 l 0))
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "b" ) )) # UInt  |-> 1)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ ((0 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 + 1 )) ”
.

Definition mpn_sub_1_safety_wit_3 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  “ ((Znth 0 l 0) >= b_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (((rp_pre + (0 * sizeof(UINT) ) )) # UInt  |-> ((Znth 0 l 0) - b_pre ))
  **  (UIntArray.undef_missing_i rp_pre 0 0 n_pre )
  **  ((( &( "cy" ) )) # UInt  |-> 0)
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "a" ) )) # UInt  |-> (Znth 0 l 0))
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "b" ) )) # UInt  |-> 0)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ ((0 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 + 1 )) ”
.

Definition mpn_sub_1_safety_wit_4 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial: (@list Z)) (b: Z) (i: Z) ,
  “ ((Znth i l 0) < b) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 < i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial) ((cons ((unsigned_last_nbits (((Znth i l 0) - b )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  ((( &( "cy" ) )) # UInt  |-> 1)
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l 0))
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "b" ) )) # UInt  |-> 1)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_sub_1_safety_wit_5 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial: (@list Z)) (b: Z) (i: Z) ,
  “ ((Znth i l 0) >= b) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 < i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial) ((cons (((Znth i l 0) - b )) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  ((( &( "cy" ) )) # UInt  |-> 0)
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l 0))
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "b" ) )) # UInt  |-> 0)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_sub_1_entail_wit_1_1 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial_2: (@list Z)) (b: Z) (i: Z) ,
  “ ((Znth i l 0) >= b) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 < i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial_2)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial_2) ((cons (((Znth i l 0) - b )) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
|--
  EX (data_rp_partial: (@list Z)) ,
  “ (0 < (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (0 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) - b_pre )) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 (i + 1 ) data_rp_partial )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
.

Definition mpn_sub_1_entail_wit_1_2 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial_2: (@list Z)) (b: Z) (i: Z) ,
  “ ((Znth i l 0) < b) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 < i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial_2)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l 0) - b )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
|--
  EX (data_rp_partial: (@list Z)) ,
  “ (0 < (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (1 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) - b_pre )) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 (i + 1 ) data_rp_partial )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
.

Definition mpn_sub_1_entail_wit_2_1 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  “ ((Znth 0 l 0) >= b_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (((rp_pre + (0 * sizeof(UINT) ) )) # UInt  |-> ((Znth 0 l 0) - b_pre ))
  **  (UIntArray.undef_missing_i rp_pre 0 0 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
|--
  EX (data_rp_partial: (@list Z)) ,
  “ (0 < (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = (0 + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (0 * (Z.pow (UINT_MOD) ((0 + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((0 + 1 )) (l)))) - b_pre )) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 (0 + 1 ) data_rp_partial )
  **  (UIntArray.undef_seg rp_pre (0 + 1 ) n_pre )
.

Definition mpn_sub_1_entail_wit_2_2 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  “ ((Znth 0 l 0) < b_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (((rp_pre + (0 * sizeof(UINT) ) )) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) - b_pre )) (32)))
  **  (UIntArray.undef_missing_i rp_pre 0 0 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
|--
  EX (data_rp_partial: (@list Z)) ,
  “ (0 < (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = (0 + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (1 * (Z.pow (UINT_MOD) ((0 + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((0 + 1 )) (l)))) - b_pre )) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 (0 + 1 ) data_rp_partial )
  **  (UIntArray.undef_seg rp_pre (0 + 1 ) n_pre )
.

Definition mpn_sub_1_return_wit_1 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial: (@list Z)) (b: Z) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (0 < i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre )) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  EX (val': Z) ,
  “ ((val' - (b * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val - b_pre )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val n_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val' n_pre )
.

Definition mpn_sub_1_partial_solve_wit_1 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) ,
  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val n_pre )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val n_pre )
  **  (UIntArray.undef_full rp_pre n_pre )
.

Definition mpn_sub_1_partial_solve_wit_2 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (((ap_pre + (0 * sizeof(UINT) ) )) # UInt  |-> (Znth 0 l 0))
  **  (UIntArray.missing_i ap_pre 0 0 n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
.

Definition mpn_sub_1_partial_solve_wit_3 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  “ ((Znth 0 l 0) < b_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ ((Znth 0 l 0) < b_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (((rp_pre + (0 * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_missing_i rp_pre 0 0 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
.

Definition mpn_sub_1_partial_solve_wit_4 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  “ ((Znth 0 l 0) >= b_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ ((Znth 0 l 0) >= b_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (((rp_pre + (0 * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_missing_i rp_pre 0 0 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
.

Definition mpn_sub_1_partial_solve_wit_5 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial: (@list Z)) (b: Z) (i: Z) ,
  “ ((Znth i l 0) < b) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 < i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre )) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((Znth i l 0) < b) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 < i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre )) ”
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
.

Definition mpn_sub_1_partial_solve_wit_6 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial: (@list Z)) (b: Z) (i: Z) ,
  “ ((Znth i l 0) >= b) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 < i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre )) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((Znth i l 0) >= b) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 < i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre )) ”
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
.

Definition mpn_sub_1_partial_solve_wit_7 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial: (@list Z)) (b: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 < i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre )) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 < i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre )) ”
  &&  (((ap_pre + (i * sizeof(UINT) ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.missing_i ap_pre i 0 n_pre l )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
.

Definition mpn_sub_1_which_implies_wit_1 := 
forall (val: Z) (n: Z) (ap: Z) ,
  (mpd_store_Z UINT_MOD ap val n )
|--
  EX (l: (@list Z)) ,
  “ ((Zlength (l)) = n) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full ap n l )
.

(*----- Function mpn_sub_n -----*)

Definition mpn_sub_n_safety_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) ,
  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_sub_n_safety_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) ,
  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_sub_n_safety_wit_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial: (@list Z)) (cy: Z) (i: Z) ,
  “ ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial) ((cons (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> (1 + 0 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_sub_n_safety_wit_4 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial: (@list Z)) (cy: Z) (i: Z) ,
  “ ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial) ((cons ((unsigned_last_nbits (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> (1 + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_sub_n_safety_wit_5 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial: (@list Z)) (cy: Z) (i: Z) ,
  “ ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial) ((cons (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> (0 + 0 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_sub_n_safety_wit_6 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial: (@list Z)) (cy: Z) (i: Z) ,
  “ ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial) ((cons ((unsigned_last_nbits (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> (0 + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_sub_n_entail_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) ,
  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  EX (data_rp_partial: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = 0) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (0 * (Z.pow (UINT_MOD) (0)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (0) (l_b)))) )) ”
  &&  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 0 data_rp_partial )
  **  (UIntArray.undef_seg rp_pre 0 n_pre )
.

Definition mpn_sub_n_entail_wit_2_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) ,
  “ ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial_2)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
|--
  EX (data_rp_partial: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - ((0 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ”
  &&  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 (i + 1 ) data_rp_partial )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
.

Definition mpn_sub_n_entail_wit_2_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) ,
  “ ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial_2)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial_2) ((cons (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
|--
  EX (data_rp_partial: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (0 + 0 )) ” 
  &&  “ ((0 + 0 ) <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - ((0 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ”
  &&  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 (i + 1 ) data_rp_partial )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
.

Definition mpn_sub_n_entail_wit_2_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) ,
  “ ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial_2)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (32))) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
|--
  EX (data_rp_partial: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (1 + 1 )) ” 
  &&  “ ((1 + 1 ) <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - ((1 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ”
  &&  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 (i + 1 ) data_rp_partial )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
.

Definition mpn_sub_n_entail_wit_2_4 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) ,
  “ ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial_2)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial_2) ((cons (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (nil)))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
|--
  EX (data_rp_partial: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (1 + 0 )) ” 
  &&  “ ((1 + 0 ) <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - ((1 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ”
  &&  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 (i + 1 ) data_rp_partial )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
.

Definition mpn_sub_n_return_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial: (@list Z)) (cy: Z) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  EX (val_r: Z) ,
  “ ((val_r - (cy * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val_a - val_b )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a n_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b n_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r n_pre )
.

Definition mpn_sub_n_partial_solve_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) ,
  “ (n_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a n_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b n_pre )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (n_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a n_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b n_pre )
  **  (UIntArray.undef_full rp_pre n_pre )
.

Definition mpn_sub_n_partial_solve_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial: (@list Z)) (cy: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (((ap_pre + (i * sizeof(UINT) ) )) # UInt  |-> (Znth i l_a 0))
  **  (UIntArray.missing_i ap_pre i 0 n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
.

Definition mpn_sub_n_partial_solve_wit_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial: (@list Z)) (cy: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (((bp_pre + (i * sizeof(UINT) ) )) # UInt  |-> (Znth i l_b 0))
  **  (UIntArray.missing_i bp_pre i 0 n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
.

Definition mpn_sub_n_partial_solve_wit_4 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial: (@list Z)) (cy: Z) (i: Z) ,
  “ ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
.

Definition mpn_sub_n_partial_solve_wit_5 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial: (@list Z)) (cy: Z) (i: Z) ,
  “ ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
.

Definition mpn_sub_n_partial_solve_wit_6 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial: (@list Z)) (cy: Z) (i: Z) ,
  “ ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
.

Definition mpn_sub_n_partial_solve_wit_7 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial: (@list Z)) (cy: Z) (i: Z) ,
  “ ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
.

Definition mpn_sub_n_which_implies_wit_1 := 
forall (val_b: Z) (val_a: Z) (n: Z) (ap: Z) (bp: Z) ,
  (mpd_store_Z UINT_MOD ap val_a n )
  **  (mpd_store_Z UINT_MOD bp val_b n )
|--
  EX (l_b: (@list Z))  (l_a: (@list Z)) ,
  “ ((Zlength (l_a)) = n) ” 
  &&  “ ((Zlength (l_b)) = n) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ”
  &&  (UIntArray.full ap n l_a )
  **  (UIntArray.full bp n l_b )
.

(*----- Function mpn_sub -----*)

Definition mpn_sub_safety_wit_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) (val_r: Z) (retval: Z) (l_r: (@list Z)) ,
  “ (an_pre > bn_pre) ” 
  &&  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (an_pre > bn_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ ((Zlength (l_r)) = bn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((val_r - (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b )) ” 
  &&  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_hi (an_pre - bn_pre ) )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  “ ((an_pre - bn_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (an_pre - bn_pre )) ”
.

Definition mpn_sub_entail_wit_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) (val_r: Z) (retval: Z) (l_r: (@list Z)) ,
  “ ((Zlength (l_r)) = bn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((val_r - (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b )) ” 
  &&  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_hi (an_pre - bn_pre ) )
  **  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ ((Zlength (l_r)) = bn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((val_r - (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b )) ” 
  &&  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_hi (an_pre - bn_pre ) )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
.

Definition mpn_sub_entail_wit_2 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) (val_r: Z) (retval: Z) (l_r: (@list Z)) ,
  “ (an_pre > bn_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ ((Zlength (l_r)) = bn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((val_r - (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b )) ” 
  &&  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_hi (an_pre - bn_pre ) )
|--
  “ (an_pre > bn_pre) ” 
  &&  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (an_pre > bn_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ ((Zlength (l_r)) = bn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((val_r - (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b )) ” 
  &&  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_hi (an_pre - bn_pre ) )
.

Definition mpn_sub_return_wit_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) (val_r: Z) (retval_2: Z) (l_r: (@list Z)) (val': Z) (retval: Z) ,
  “ ((val' - (retval * (Z.pow (UINT_MOD) ((an_pre - bn_pre ))) ) ) = (val_a_hi - retval_2 )) ” 
  &&  “ (an_pre > bn_pre) ” 
  &&  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (an_pre > bn_pre) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= UINT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ ((Zlength (l_r)) = bn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((val_r - (retval_2 * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b )) ” 
  &&  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_hi (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (rp_pre + (bn_pre * sizeof(UINT) ) ) val' (an_pre - bn_pre ) )
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
|--
  EX (val_r_out: Z) ,
  “ ((val_r_out - (retval * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a - val_b )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out an_pre )
.

Definition mpn_sub_return_wit_2 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) (val_r: Z) (retval: Z) (l_r: (@list Z)) ,
  “ (an_pre <= bn_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ ((Zlength (l_r)) = bn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((val_r - (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b )) ” 
  &&  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_hi (an_pre - bn_pre ) )
|--
  EX (val_r_out: Z) ,
  “ ((val_r_out - (retval * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a - val_b )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out an_pre )
.

Definition mpn_sub_partial_solve_wit_1_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) ,
  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
|--
  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
.

Definition mpn_sub_partial_solve_wit_1_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) ,
  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
|--
  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
.

Definition mpn_sub_partial_solve_wit_1 := mpn_sub_partial_solve_wit_1_pure -> mpn_sub_partial_solve_wit_1_aux.

Definition mpn_sub_partial_solve_wit_2_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) ,
  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_hi (an_pre - bn_pre ) )
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
|--
  “ (an_pre >= bn_pre) ” 
  &&  “ (bn_pre >= 0) ”
.

Definition mpn_sub_partial_solve_wit_2_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) ,
  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_hi (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
|--
  “ (an_pre >= bn_pre) ” 
  &&  “ (bn_pre >= 0) ” 
  &&  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (UIntArray.undef_full rp_pre an_pre )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_hi (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
.

Definition mpn_sub_partial_solve_wit_2 := mpn_sub_partial_solve_wit_2_pure -> mpn_sub_partial_solve_wit_2_aux.

Definition mpn_sub_partial_solve_wit_3_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) ,
  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.undef_full rp_pre bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_hi (an_pre - bn_pre ) )
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
|--
  “ (bn_pre >= 0) ”
.

Definition mpn_sub_partial_solve_wit_3_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) ,
  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (UIntArray.undef_full rp_pre bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_hi (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
|--
  “ (bn_pre >= 0) ” 
  &&  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_hi (an_pre - bn_pre ) )
.

Definition mpn_sub_partial_solve_wit_3 := mpn_sub_partial_solve_wit_3_pure -> mpn_sub_partial_solve_wit_3_aux.

Definition mpn_sub_partial_solve_wit_4 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) (val_r: Z) (retval: Z) ,
  “ ((val_r - (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b )) ” 
  &&  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_hi (an_pre - bn_pre ) )
|--
  “ ((val_r - (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b )) ” 
  &&  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD rp_pre val_r bn_pre )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_hi (an_pre - bn_pre ) )
.

Definition mpn_sub_partial_solve_wit_5_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) (val_r: Z) (retval: Z) (l_r: (@list Z)) ,
  “ (an_pre > bn_pre) ” 
  &&  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (an_pre > bn_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ ((Zlength (l_r)) = bn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((val_r - (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b )) ” 
  &&  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_hi (an_pre - bn_pre ) )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ”
.

Definition mpn_sub_partial_solve_wit_5_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) (val_r: Z) (retval: Z) (l_r: (@list Z)) ,
  “ (an_pre > bn_pre) ” 
  &&  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (an_pre > bn_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ ((Zlength (l_r)) = bn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((val_r - (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b )) ” 
  &&  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_hi (an_pre - bn_pre ) )
|--
  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre > bn_pre) ” 
  &&  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (an_pre > bn_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ ((Zlength (l_r)) = bn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((val_r - (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b )) ” 
  &&  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_hi (an_pre - bn_pre ) )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
.

Definition mpn_sub_partial_solve_wit_5 := mpn_sub_partial_solve_wit_5_pure -> mpn_sub_partial_solve_wit_5_aux.

Definition mpn_sub_which_implies_wit_1 := 
forall (val_a: Z) (an: Z) (bn: Z) (ap: Z) ,
  “ (an >= bn) ” 
  &&  “ (an > 0) ” 
  &&  “ (bn >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap val_a an )
|--
  EX (val_a_hi: Z)  (val_a_lo: Z) ,
  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn)) ) )) ”
  &&  (mpd_store_Z UINT_MOD ap val_a_lo bn )
  **  (mpd_store_Z UINT_MOD (ap + (bn * sizeof(UINT) ) ) val_a_hi (an - bn ) )
.

Definition mpn_sub_which_implies_wit_2 := 
forall (an: Z) (bn: Z) (rp: Z) ,
  “ (an >= bn) ” 
  &&  “ (bn >= 0) ”
  &&  (UIntArray.undef_full rp an )
|--
  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_full (rp + (bn * sizeof(UINT) ) ) (an - bn ) )
.

Definition mpn_sub_which_implies_wit_3 := 
forall (val_r_out: Z) (bn: Z) (rp: Z) ,
  (mpd_store_Z UINT_MOD rp val_r_out bn )
|--
  EX (l_r: (@list Z)) ,
  “ ((Zlength (l_r)) = bn) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r_out) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ”
  &&  (UIntArray.full rp bn l_r )
.

(*----- Function mpz_clear -----*)

Definition mpz_clear_return_wit_1 := 
forall (r_pre: Z) (n: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) ,
  “ (same_sign n size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (cap_2 <> 0) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
|--
  EX (ptr: Z)  (cap: Z)  (size: Z) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_clear_return_wit_2 := 
forall (r_pre: Z) (n: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) ,
  “ (same_sign n size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (cap_2 = 0) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (n)) (Zabs (size_2)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
|--
  EX (ptr: Z)  (cap: Z)  (size: Z) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_clear_partial_solve_wit_1 := 
forall (r_pre: Z) (n: Z) ,
  (store_Z r_pre n )
|--
  EX (cap: Z)  (size: Z)  (ptr: Z) ,
  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
.

Definition mpz_clear_partial_solve_wit_2 := 
forall (r_pre: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) ,
  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (cap <> 0) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
|--
  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (cap <> 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
.

(*----- Function mpz_realloc -----*)

Definition mpz_realloc_safety_wit_1 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) ,
  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ”
  &&  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_realloc_safety_wit_2 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  “ (retval_3 > retval) ” 
  &&  “ (retval_3 = (Zabs (old))) ” 
  &&  “ (retval = (Z.max (size_pre) (1))) ” 
  &&  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ” 
  &&  “ (cap = 0) ”
  &&  (UIntArray.undef_full retval_2 retval )
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_realloc_safety_wit_3 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  “ (retval_3 > retval) ” 
  &&  “ (retval_3 = (Zabs (old))) ” 
  &&  “ (retval = (Z.max (size_pre) (1))) ” 
  &&  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ” 
  &&  “ (cap <> 0) ”
  &&  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (old)) retval )
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_realloc_return_wit_1 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval_2: Z) (retval: Z) (retval_3: Z) ,
  “ (retval_3 <= retval_2) ” 
  &&  “ (retval_3 = (Zabs (old))) ” 
  &&  “ (retval_2 = (Z.max (size_pre) (1))) ” 
  &&  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ” 
  &&  “ (cap = 0) ”
  &&  (UIntArray.undef_full retval retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  EX (r_pre__mp_alloc: Z) ,
  “ (same_sign n old ) ” 
  &&  “ (r_pre__mp_alloc = (Z.max (size_pre) (1))) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
.

Definition mpz_realloc_return_wit_2 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval_2: Z) (retval: Z) (retval_3: Z) ,
  “ (retval_3 <= retval_2) ” 
  &&  “ (retval_3 = (Zabs (old))) ” 
  &&  “ (retval_2 = (Z.max (size_pre) (1))) ” 
  &&  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ” 
  &&  “ (cap <> 0) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) retval_2 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  EX (r_pre__mp_alloc: Z) ,
  “ (same_sign n old ) ” 
  &&  “ (r_pre__mp_alloc = (Z.max (size_pre) (1))) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
.

Definition mpz_realloc_return_wit_3 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval_2: Z) (retval: Z) (retval_3: Z) ,
  “ (retval_3 > retval_2) ” 
  &&  “ (retval_3 = (Zabs (old))) ” 
  &&  “ (retval_2 = (Z.max (size_pre) (1))) ” 
  &&  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ” 
  &&  “ (cap <> 0) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) retval_2 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  EX (r_pre__mp_alloc: Z) ,
  “ (same_sign n old ) ” 
  &&  “ (r_pre__mp_alloc = (Z.max (size_pre) (1))) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
.

Definition mpz_realloc_return_wit_4 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval_2: Z) (retval: Z) (retval_3: Z) ,
  “ (retval_3 > retval_2) ” 
  &&  “ (retval_3 = (Zabs (old))) ” 
  &&  “ (retval_2 = (Z.max (size_pre) (1))) ” 
  &&  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ” 
  &&  “ (cap = 0) ”
  &&  (UIntArray.undef_full retval retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  EX (r_pre__mp_alloc: Z) ,
  “ (same_sign n old ) ” 
  &&  “ (r_pre__mp_alloc = (Z.max (size_pre) (1))) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
.

Definition mpz_realloc_partial_solve_wit_1 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) ,
  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_realloc_partial_solve_wit_2_pure := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) ,
  “ (retval = (Z.max (size_pre) (1))) ” 
  &&  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ” 
  &&  “ (cap <> 0) ”
  &&  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  “ (cap >= 0) ” 
  &&  “ (retval >= cap) ” 
  &&  “ ((Z.max (size_pre) (1)) >= cap) ”
.

Definition mpz_realloc_partial_solve_wit_2_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) ,
  “ (retval = (Z.max (size_pre) (1))) ” 
  &&  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ” 
  &&  “ (cap <> 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  “ (cap >= 0) ” 
  &&  “ (retval >= cap) ” 
  &&  “ ((Z.max (size_pre) (1)) >= cap) ” 
  &&  “ (retval = (Z.max (size_pre) (1))) ” 
  &&  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ” 
  &&  “ (cap <> 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_realloc_partial_solve_wit_2 := mpz_realloc_partial_solve_wit_2_pure -> mpz_realloc_partial_solve_wit_2_aux.

Definition mpz_realloc_partial_solve_wit_3_pure := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) ,
  “ (retval = (Z.max (size_pre) (1))) ” 
  &&  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ” 
  &&  “ (cap = 0) ”
  &&  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  “ (retval >= 0) ”
.

Definition mpz_realloc_partial_solve_wit_3_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) ,
  “ (retval = (Z.max (size_pre) (1))) ” 
  &&  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ” 
  &&  “ (cap = 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  “ (retval >= 0) ” 
  &&  “ (retval = (Z.max (size_pre) (1))) ” 
  &&  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ” 
  &&  “ (cap = 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_realloc_partial_solve_wit_3 := mpz_realloc_partial_solve_wit_3_pure -> mpz_realloc_partial_solve_wit_3_aux.

Definition mpz_realloc_partial_solve_wit_4_pure := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval: Z) (retval_2: Z) ,
  “ (retval = (Z.max (size_pre) (1))) ” 
  &&  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ” 
  &&  “ (cap <> 0) ”
  &&  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (old)) retval )
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (old <= INT_MAX) ” 
  &&  “ (INT_MIN < old) ”
.

Definition mpz_realloc_partial_solve_wit_4_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval: Z) (retval_2: Z) ,
  “ (retval = (Z.max (size_pre) (1))) ” 
  &&  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ” 
  &&  “ (cap <> 0) ”
  &&  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (old)) retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (old <= INT_MAX) ” 
  &&  “ (INT_MIN < old) ” 
  &&  “ (retval = (Z.max (size_pre) (1))) ” 
  &&  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ” 
  &&  “ (cap <> 0) ”
  &&  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (old)) retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
.

Definition mpz_realloc_partial_solve_wit_4 := mpz_realloc_partial_solve_wit_4_pure -> mpz_realloc_partial_solve_wit_4_aux.

Definition mpz_realloc_partial_solve_wit_5_pure := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (retval_2: Z) ,
  “ (retval = (Z.max (size_pre) (1))) ” 
  &&  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ” 
  &&  “ (cap = 0) ”
  &&  (UIntArray.undef_full retval_2 retval )
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (old <= INT_MAX) ” 
  &&  “ (INT_MIN < old) ”
.

Definition mpz_realloc_partial_solve_wit_5_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (retval_2: Z) ,
  “ (retval = (Z.max (size_pre) (1))) ” 
  &&  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ” 
  &&  “ (cap = 0) ”
  &&  (UIntArray.undef_full retval_2 retval )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (old <= INT_MAX) ” 
  &&  “ (INT_MIN < old) ” 
  &&  “ (retval = (Z.max (size_pre) (1))) ” 
  &&  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ” 
  &&  “ (cap = 0) ”
  &&  (UIntArray.undef_full retval_2 retval )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
.

Definition mpz_realloc_partial_solve_wit_5 := mpz_realloc_partial_solve_wit_5_pure -> mpz_realloc_partial_solve_wit_5_aux.

(*----- Function mrz_realloc_if -----*)

Definition mrz_realloc_if_return_wit_1 := 
forall (n_pre: Z) (z_pre: Z) (m: Z) (cap: Z) (old: Z) (ptr: Z) ,
  “ (n_pre <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign m old ) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  EX (z_pre__mp_alloc: Z) ,
  “ (same_sign m old ) ” 
  &&  “ (z_pre__mp_alloc = (Z.max ((Z.max (n_pre) (1))) (cap))) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) (Z.max ((Z.max (n_pre) (1))) (cap)) )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_pre__mp_alloc)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mrz_realloc_if_return_wit_2 := 
forall (n_pre: Z) (z_pre: Z) (m: Z) (cap: Z) (old: Z) (r_callee__mp_alloc: Z) (retval: Z) ,
  “ (same_sign m old ) ” 
  &&  “ (r_callee__mp_alloc = (Z.max (n_pre) (1))) ” 
  &&  “ (n_pre > cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign m old ) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (n_pre) (1)) )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_callee__mp_alloc)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  EX (z_pre__mp_alloc: Z) ,
  “ (same_sign m old ) ” 
  &&  “ (z_pre__mp_alloc = (Z.max ((Z.max (n_pre) (1))) (cap))) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max ((Z.max (n_pre) (1))) (cap)) )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_pre__mp_alloc)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
.

Definition mrz_realloc_if_partial_solve_wit_1_pure := 
forall (n_pre: Z) (z_pre: Z) (m: Z) (cap: Z) (old: Z) (ptr: Z) ,
  “ (n_pre > cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign m old ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Ptr  |-> z_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  “ (n_pre >= cap) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign m old ) ”
.

Definition mrz_realloc_if_partial_solve_wit_1_aux := 
forall (n_pre: Z) (z_pre: Z) (m: Z) (cap: Z) (old: Z) (ptr: Z) ,
  “ (n_pre > cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign m old ) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  “ (n_pre >= cap) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign m old ) ” 
  &&  “ (n_pre > cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign m old ) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mrz_realloc_if_partial_solve_wit_1 := mrz_realloc_if_partial_solve_wit_1_pure -> mrz_realloc_if_partial_solve_wit_1_aux.

(*----- Function mpz_sgn -----*)

Definition mpz_sgn_safety_wit_1 := 
forall (u_pre: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) ,
  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_sgn_return_wit_1 := 
forall (u_pre: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) ,
  “ (size > 0) ” 
  &&  “ (retval = 1) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
|--
  (“ (n < 0) ” 
  &&  “ (retval = (-1)) ”
  &&  (store_Z u_pre n ))
  ||
  (“ (n = 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_Z u_pre n ))
  ||
  (“ (n > 0) ” 
  &&  “ (retval = 1) ”
  &&  (store_Z u_pre n ))
.

Definition mpz_sgn_return_wit_2 := 
forall (u_pre: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) ,
  “ (size = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
|--
  (“ (n < 0) ” 
  &&  “ (retval = (-1)) ”
  &&  (store_Z u_pre n ))
  ||
  (“ (n = 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_Z u_pre n ))
  ||
  (“ (n > 0) ” 
  &&  “ (retval = 1) ”
  &&  (store_Z u_pre n ))
.

Definition mpz_sgn_return_wit_3 := 
forall (u_pre: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) ,
  “ (size < 0) ” 
  &&  “ (retval = (-1)) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
|--
  (“ (n < 0) ” 
  &&  “ (retval = (-1)) ”
  &&  (store_Z u_pre n ))
  ||
  (“ (n = 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_Z u_pre n ))
  ||
  (“ (n > 0) ” 
  &&  “ (retval = 1) ”
  &&  (store_Z u_pre n ))
.

Definition mpz_sgn_partial_solve_wit_1 := 
forall (u_pre: Z) (n: Z) ,
  (store_Z u_pre n )
|--
  EX (cap: Z)  (size: Z)  (ptr: Z) ,
  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
.

Definition mpz_sgn_partial_solve_wit_2 := 
forall (u_pre: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) ,
  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
|--
  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
.

(*----- Function mpz_swap -----*)

Definition mpz_swap_return_wit_1 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) ,
  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
|--
  (store_Z u_pre m )
  **  (store_Z v_pre n )
.

Definition mpz_swap_partial_solve_wit_1 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) ,
  (store_Z u_pre n )
  **  (store_Z v_pre m )
|--
  EX (cap_2: Z)  (size_2: Z)  (ptr_2: Z)  (cap: Z)  (size: Z)  (ptr: Z) ,
  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
.

Definition mpz_swap_partial_solve_wit_2 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) ,
  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
|--
  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
.

Definition mpz_swap_partial_solve_wit_3 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) ,
  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
|--
  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
.

(*----- Function mpz_abs_add -----*)

Definition mpz_abs_add_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rptr: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) ,
  “ (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) (nil)))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) (nil)))) ) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (asize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (an <= acap) ” 
  &&  “ (bn <= bcap) ” 
  &&  “ (same_sign n_new asize ) ” 
  &&  “ (same_sign m_new bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (rcap >= 0) ”
  &&  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
|--
  “ ((an + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (an + 1 )) ”
.

Definition mpz_abs_add_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rptr: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) ,
  “ (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) (nil)))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) (nil)))) ) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (asize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (an <= acap) ” 
  &&  “ (bn <= bcap) ” 
  &&  “ (same_sign n_new asize ) ” 
  &&  “ (same_sign m_new bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (rcap >= 0) ”
  &&  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_abs_add_entail_wit_1_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) ,
  “ (retval < retval_2) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  EX (rptr: Z)  (bptr: Z)  (aptr: Z)  (rcap: Z)  (rsize: Z)  (bcap: Z)  (acap: Z)  (bsize: Z)  (asize: Z)  (n_new: Z)  (m_new: Z) ,
  “ (Permutation (cons ((Prod2 (b_pre) (n_new))) ((cons ((Prod2 (a_pre) (m_new))) (nil)))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) (nil)))) ) ” 
  &&  “ (retval_2 >= retval) ” 
  &&  “ (retval_2 = (Zabs (asize))) ” 
  &&  “ (retval = (Zabs (bsize))) ” 
  &&  “ (retval_2 <= acap) ” 
  &&  “ (retval <= bcap) ” 
  &&  “ (same_sign n_new asize ) ” 
  &&  “ (same_sign m_new bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (rcap >= 0) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg aptr retval_2 acap )
  **  (UIntArray.undef_seg bptr retval bcap )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) retval_2 )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) retval )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
.

Definition mpz_abs_add_entail_wit_1_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) ,
  “ (retval >= retval_2) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  EX (rptr: Z)  (bptr: Z)  (aptr: Z)  (rcap: Z)  (rsize: Z)  (bcap: Z)  (acap: Z)  (bsize: Z)  (asize: Z)  (n_new: Z)  (m_new: Z) ,
  “ (Permutation (cons ((Prod2 (a_pre) (n_new))) ((cons ((Prod2 (b_pre) (m_new))) (nil)))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) (nil)))) ) ” 
  &&  “ (retval >= retval_2) ” 
  &&  “ (retval = (Zabs (asize))) ” 
  &&  “ (retval_2 = (Zabs (bsize))) ” 
  &&  “ (retval <= acap) ” 
  &&  “ (retval_2 <= bcap) ” 
  &&  “ (same_sign n_new asize ) ” 
  &&  “ (same_sign m_new bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (rcap >= 0) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg aptr retval acap )
  **  (UIntArray.undef_seg bptr retval_2 bcap )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) retval_2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
.

Definition mpz_abs_add_entail_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new_2: Z) (m_new_2: Z) (aptr_2: Z) (bptr_2: Z) (asize_2: Z) (bsize_2: Z) (acap_2: Z) (bcap_2: Z) (rsize_2: Z) (rcap_2: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (z_callee__mp_alloc: Z) (retval: Z) ,
  “ (same_sign l rsize_2 ) ” 
  &&  “ (z_callee__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap_2))) ” 
  &&  “ (Permutation (cons ((Prod2 (a) (n_new_2))) ((cons ((Prod2 (b) (m_new_2))) (nil)))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) (nil)))) ) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (asize_2))) ” 
  &&  “ (bn = (Zabs (bsize_2))) ” 
  &&  “ (an <= acap_2) ” 
  &&  “ (bn <= bcap_2) ” 
  &&  “ (same_sign n_new_2 asize_2 ) ” 
  &&  “ (same_sign m_new_2 bsize_2 ) ” 
  &&  “ ((Zabs (rsize_2)) <= rcap_2) ” 
  &&  “ (same_sign l rsize_2 ) ” 
  &&  “ (rcap_2 >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (l)) (Zabs (rsize_2)) )
  **  (UIntArray.undef_seg retval (Zabs (rsize_2)) (Z.max ((Z.max ((an + 1 )) (1))) (rcap_2)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr_2)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize_2)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap_2)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr_2)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize_2)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap_2)
  **  (UIntArray.undef_seg aptr_2 an acap_2 )
  **  (UIntArray.undef_seg bptr_2 bn bcap_2 )
  **  (mpd_store_Z_compact UINT_MOD aptr_2 (Zabs (n_new_2)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr_2 (Zabs (m_new_2)) bn )
|--
  EX (bptr: Z)  (aptr: Z)  (r__mp_d: Z)  (r__mp_alloc: Z)  (rcap: Z)  (rsize: Z)  (bcap: Z)  (acap: Z)  (bsize: Z)  (asize: Z)  (n_new: Z)  (m_new: Z) ,
  “ (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) (nil)))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) (nil)))) ) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (asize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (an <= acap) ” 
  &&  “ (bn <= bcap) ” 
  &&  “ (same_sign n_new asize ) ” 
  &&  “ (same_sign m_new bsize ) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ” 
  &&  “ (r__mp_d = retval) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (UIntArray.undef_full retval an )
  **  (UIntArray.undef_seg retval an (Z.max ((Z.max ((an + 1 )) (1))) (rcap)) )
.

Definition mpz_abs_add_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (val_r_out: Z) (retval: Z) ,
  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n_new)) + (Zabs (m_new)) )) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (m_new)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (n_new)) an ) ” 
  &&  “ (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) (nil)))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) (nil)))) ) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (asize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (an <= acap) ” 
  &&  “ (bn <= bcap) ” 
  &&  “ (same_sign n_new asize ) ” 
  &&  “ (same_sign m_new bsize ) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  (((rp + (an * sizeof(UINT) ) )) # UInt  |-> retval)
  **  (UIntArray.undef_seg rp (an + 1 ) (Z.max ((Z.max ((an + 1 )) (1))) (rcap)) )
  **  (mpd_store_Z UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z UINT_MOD rp val_r_out an )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) (signed_last_nbits (((unsigned_last_nbits (an) (32)) + retval )) (32)) )
.

Definition mpz_abs_add_partial_solve_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) ,
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  EX (cap: Z)  (size: Z)  (ptr: Z) ,
  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
.

Definition mpz_abs_add_partial_solve_wit_2_pure := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) ,
  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ”
.

Definition mpz_abs_add_partial_solve_wit_2_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) ,
  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
.

Definition mpz_abs_add_partial_solve_wit_2 := mpz_abs_add_partial_solve_wit_2_pure -> mpz_abs_add_partial_solve_wit_2_aux.

Definition mpz_abs_add_partial_solve_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) ,
  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  EX (cap_2: Z)  (size_2: Z)  (ptr_2: Z) ,
  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
.

Definition mpz_abs_add_partial_solve_wit_4_pure := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size_2: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size: Z) (cap_2: Z) ,
  “ (same_sign m size ) ” 
  &&  “ ((Zabs (size)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size_2))) ” 
  &&  “ (same_sign n size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |->_)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_2)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ”
.

Definition mpz_abs_add_partial_solve_wit_4_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size_2: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size: Z) (cap_2: Z) ,
  “ (same_sign m size ) ” 
  &&  “ ((Zabs (size)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size_2))) ” 
  &&  “ (same_sign n size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_2)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ” 
  &&  “ (same_sign m size ) ” 
  &&  “ ((Zabs (size)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size_2))) ” 
  &&  “ (same_sign n size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_2)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
.

Definition mpz_abs_add_partial_solve_wit_4 := mpz_abs_add_partial_solve_wit_4_pure -> mpz_abs_add_partial_solve_wit_4_aux.

Definition mpz_abs_add_partial_solve_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) ,
  “ (retval < retval_2) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  “ (retval < retval_2) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
.

Definition mpz_abs_add_partial_solve_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) ,
  “ (retval < retval_2) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  “ (retval < retval_2) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
.

Definition mpz_abs_add_partial_solve_wit_7_pure := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rptr: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) ,
  “ (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) (nil)))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) (nil)))) ) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (asize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (an <= acap) ” 
  &&  “ (bn <= bcap) ” 
  &&  “ (same_sign n_new asize ) ” 
  &&  “ (same_sign m_new bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (rcap >= 0) ”
  &&  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
|--
  “ (rcap >= 0) ” 
  &&  “ ((an + 1 ) >= 1) ” 
  &&  “ ((an + 1 ) <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (((Zabs (asize)) + 1 ) <= INT_MAX) ” 
  &&  “ (((Zabs (asize)) + 1 ) >= 1) ” 
  &&  “ (rcap <= INT_MAX) ”
.

Definition mpz_abs_add_partial_solve_wit_7_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rptr: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) ,
  “ (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) (nil)))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) (nil)))) ) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (asize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (an <= acap) ” 
  &&  “ (bn <= bcap) ” 
  &&  “ (same_sign n_new asize ) ” 
  &&  “ (same_sign m_new bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (rcap >= 0) ”
  &&  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
|--
  “ (rcap >= 0) ” 
  &&  “ ((an + 1 ) >= 1) ” 
  &&  “ ((an + 1 ) <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (((Zabs (asize)) + 1 ) <= INT_MAX) ” 
  &&  “ (((Zabs (asize)) + 1 ) >= 1) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) (nil)))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) (nil)))) ) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (asize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (an <= acap) ” 
  &&  “ (bn <= bcap) ” 
  &&  “ (same_sign n_new asize ) ” 
  &&  “ (same_sign m_new bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (rcap >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
.

Definition mpz_abs_add_partial_solve_wit_7 := mpz_abs_add_partial_solve_wit_7_pure -> mpz_abs_add_partial_solve_wit_7_aux.

Definition mpz_abs_add_partial_solve_wit_8_pure := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) ,
  “ (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) (nil)))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) (nil)))) ) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (asize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (an <= acap) ” 
  &&  “ (bn <= bcap) ” 
  &&  “ (same_sign n_new asize ) ” 
  &&  “ (same_sign m_new bsize ) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max ((an + 1 )) (1))) (rcap)) )
|--
  “ (an >= bn) ” 
  &&  “ (an >= 0) ” 
  &&  “ (bn >= 0) ” 
  &&  “ ((Zabs (bsize)) >= 0) ” 
  &&  “ ((Zabs (asize)) >= 0) ”
.

Definition mpz_abs_add_partial_solve_wit_8_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) ,
  “ (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) (nil)))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) (nil)))) ) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (asize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (an <= acap) ” 
  &&  “ (bn <= bcap) ” 
  &&  “ (same_sign n_new asize ) ” 
  &&  “ (same_sign m_new bsize ) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max ((an + 1 )) (1))) (rcap)) )
|--
  “ (an >= bn) ” 
  &&  “ (an >= 0) ” 
  &&  “ (bn >= 0) ” 
  &&  “ ((Zabs (bsize)) >= 0) ” 
  &&  “ ((Zabs (asize)) >= 0) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (m_new)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (n_new)) an ) ” 
  &&  “ (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) (nil)))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) (nil)))) ) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (asize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (an <= acap) ” 
  &&  “ (bn <= bcap) ” 
  &&  “ (same_sign n_new asize ) ” 
  &&  “ (same_sign m_new bsize ) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (m_new)) bn )
  **  (UIntArray.undef_full rp an )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max ((an + 1 )) (1))) (rcap)) )
.

Definition mpz_abs_add_partial_solve_wit_8 := mpz_abs_add_partial_solve_wit_8_pure -> mpz_abs_add_partial_solve_wit_8_aux.

Definition mpz_abs_add_partial_solve_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (val_r_out: Z) (retval: Z) ,
  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n_new)) + (Zabs (m_new)) )) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (m_new)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (n_new)) an ) ” 
  &&  “ (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) (nil)))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) (nil)))) ) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (asize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (an <= acap) ” 
  &&  “ (bn <= bcap) ” 
  &&  “ (same_sign n_new asize ) ” 
  &&  “ (same_sign m_new bsize ) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z UINT_MOD rp val_r_out an )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max ((an + 1 )) (1))) (rcap)) )
|--
  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n_new)) + (Zabs (m_new)) )) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (m_new)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (n_new)) an ) ” 
  &&  “ (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) (nil)))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) (nil)))) ) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (asize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (an <= acap) ” 
  &&  “ (bn <= bcap) ” 
  &&  “ (same_sign n_new asize ) ” 
  &&  “ (same_sign m_new bsize ) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  (((rp + (an * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_seg rp (an + 1 ) (Z.max ((Z.max ((an + 1 )) (1))) (rcap)) )
  **  (mpd_store_Z UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z UINT_MOD rp val_r_out an )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
.

(*----- Function mpz_abs_sub -----*)

Definition mpz_abs_sub_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) ,
  “ ((Zabs (n)) > (Zabs (m))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) ,
  “ ((Zabs (n)) = (Zabs (m))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) ,
  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (retval_3 = (-1)) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) ,
  “ (retval_3 <= 0) ” 
  &&  “ ((Zabs (n)) > (Zabs (m))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ False ”
.

Definition mpz_abs_sub_safety_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) ,
  “ (retval_3 > 0) ” 
  &&  “ ((Zabs (n)) = (Zabs (m))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ False ”
.

Definition mpz_abs_sub_safety_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) ,
  “ (retval_3 > 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (retval_3 = (-1)) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ False ”
.

Definition mpz_abs_sub_safety_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) ,
  “ (retval_3 <= 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (retval_3 = (-1)) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_safety_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) ,
  “ (retval_3 <= 0) ” 
  &&  “ ((Zabs (n)) = (Zabs (m))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_safety_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) ,
  “ (retval_3 >= 0) ” 
  &&  “ (retval_3 <= 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (retval_3 = (-1)) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ False ”
.

Definition mpz_abs_sub_safety_wit_10 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) ,
  “ (retval_3 < 0) ” 
  &&  “ (retval_3 <= 0) ” 
  &&  “ ((Zabs (n)) = (Zabs (m))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ False ”
.

Definition mpz_abs_sub_safety_wit_11 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= bn) ” 
  &&  “ ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m)) - (Zabs (n)) )) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (m)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (n)) an ) ” 
  &&  “ (cmp < 0) ” 
  &&  “ (cmp <= 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z_compact UINT_MOD rp val_r_out retval )
  **  (UIntArray.undef_seg rp retval bn )
  **  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (retval <> (INT_MIN)) ”
.

Definition mpz_abs_sub_safety_wit_12 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) ,
  “ (retval_3 >= 0) ” 
  &&  “ (retval_3 <= 0) ” 
  &&  “ ((Zabs (n)) = (Zabs (m))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_entail_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) ,
  “ (retval_3 > 0) ” 
  &&  “ ((Zabs (n)) > (Zabs (m))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  EX (rptr: Z)  (b_pre__mp_d: Z)  (a_pre__mp_d: Z)  (rcap: Z)  (rsize: Z)  (a_pre__mp_alloc: Z)  (a_pre__mp_size: Z)  (b_pre__mp_alloc: Z)  (b_pre__mp_size: Z) ,
  “ (retval_3 > 0) ” 
  &&  “ ((Zabs (n)) > (Zabs (m))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (retval_2 = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (retval = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (rcap >= 0) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) retval )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) retval_2 )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
.

Definition mpz_abs_sub_entail_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize_2: Z) (rcap_2: Z) (cmp: Z) (bn: Z) (b_pre__mp_size_2: Z) (b_pre__mp_alloc_2: Z) (an: Z) (a_pre__mp_size_2: Z) (a_pre__mp_alloc_2: Z) (a_pre__mp_d_2: Z) (b_pre__mp_d_2: Z) (z_callee__mp_alloc: Z) (retval: Z) ,
  “ (same_sign l rsize_2 ) ” 
  &&  “ (z_callee__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap_2))) ” 
  &&  “ (cmp > 0) ” 
  &&  “ ((Zabs (n)) > (Zabs (m))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size_2))) ” 
  &&  “ (same_sign m b_pre__mp_size_2 ) ” 
  &&  “ ((Zabs (b_pre__mp_size_2)) <= b_pre__mp_alloc_2) ” 
  &&  “ (an = (Zabs (a_pre__mp_size_2))) ” 
  &&  “ (same_sign n a_pre__mp_size_2 ) ” 
  &&  “ ((Zabs (a_pre__mp_size_2)) <= a_pre__mp_alloc_2) ” 
  &&  “ ((Zabs (rsize_2)) <= rcap_2) ” 
  &&  “ (same_sign l rsize_2 ) ” 
  &&  “ (rcap_2 >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (l)) (Zabs (rsize_2)) )
  **  (UIntArray.undef_seg retval (Zabs (rsize_2)) (Z.max ((Z.max (an) (1))) (rcap_2)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d_2)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d_2 (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d_2)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d_2 (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d_2 (Zabs (b_pre__mp_size_2)) b_pre__mp_alloc_2 )
  **  (UIntArray.undef_seg a_pre__mp_d_2 (Zabs (a_pre__mp_size_2)) a_pre__mp_alloc_2 )
|--
  EX (b_pre__mp_d: Z)  (a_pre__mp_d: Z)  (r__mp_d: Z)  (r__mp_alloc: Z)  (rcap: Z)  (rsize: Z)  (a_pre__mp_alloc: Z)  (a_pre__mp_size: Z)  (b_pre__mp_alloc: Z)  (b_pre__mp_size: Z) ,
  “ (cmp > 0) ” 
  &&  “ ((Zabs (n)) > (Zabs (m))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap))) ” 
  &&  “ (r__mp_d = retval) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_full retval an )
  **  (UIntArray.undef_seg retval an (Z.max ((Z.max (an) (1))) (rcap)) )
.

Definition mpz_abs_sub_entail_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) ,
  “ (retval_3 < 0) ” 
  &&  “ (retval_3 <= 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (retval_3 = (-1)) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  EX (rptr: Z)  (b_pre__mp_d: Z)  (a_pre__mp_d: Z)  (rcap: Z)  (rsize: Z)  (a_pre__mp_alloc: Z)  (a_pre__mp_size: Z)  (b_pre__mp_alloc: Z)  (b_pre__mp_size: Z) ,
  “ (retval_3 < 0) ” 
  &&  “ (retval_3 <= 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (retval_3 = (-1)) ” 
  &&  “ (retval_2 = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (retval = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (rcap >= 0) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) retval )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) retval_2 )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
.

Definition mpz_abs_sub_entail_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize_2: Z) (rcap_2: Z) (cmp: Z) (bn: Z) (b_pre__mp_size_2: Z) (b_pre__mp_alloc_2: Z) (an: Z) (a_pre__mp_size_2: Z) (a_pre__mp_alloc_2: Z) (a_pre__mp_d_2: Z) (b_pre__mp_d_2: Z) (z_callee__mp_alloc: Z) (retval: Z) ,
  “ (same_sign l rsize_2 ) ” 
  &&  “ (z_callee__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap_2))) ” 
  &&  “ (cmp < 0) ” 
  &&  “ (cmp <= 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size_2))) ” 
  &&  “ (same_sign m b_pre__mp_size_2 ) ” 
  &&  “ ((Zabs (b_pre__mp_size_2)) <= b_pre__mp_alloc_2) ” 
  &&  “ (an = (Zabs (a_pre__mp_size_2))) ” 
  &&  “ (same_sign n a_pre__mp_size_2 ) ” 
  &&  “ ((Zabs (a_pre__mp_size_2)) <= a_pre__mp_alloc_2) ” 
  &&  “ ((Zabs (rsize_2)) <= rcap_2) ” 
  &&  “ (same_sign l rsize_2 ) ” 
  &&  “ (rcap_2 >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (l)) (Zabs (rsize_2)) )
  **  (UIntArray.undef_seg retval (Zabs (rsize_2)) (Z.max ((Z.max (bn) (1))) (rcap_2)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d_2)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d_2 (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d_2)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d_2 (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d_2 (Zabs (b_pre__mp_size_2)) b_pre__mp_alloc_2 )
  **  (UIntArray.undef_seg a_pre__mp_d_2 (Zabs (a_pre__mp_size_2)) a_pre__mp_alloc_2 )
|--
  EX (b_pre__mp_d: Z)  (a_pre__mp_d: Z)  (r__mp_d: Z)  (r__mp_alloc: Z)  (rcap: Z)  (rsize: Z)  (a_pre__mp_alloc: Z)  (a_pre__mp_size: Z)  (b_pre__mp_alloc: Z)  (b_pre__mp_size: Z) ,
  “ (cmp < 0) ” 
  &&  “ (cmp <= 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap))) ” 
  &&  “ (r__mp_d = retval) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap))) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_full retval bn )
  **  (UIntArray.undef_seg retval bn (Z.max ((Z.max (bn) (1))) (rcap)) )
.

Definition mpz_abs_sub_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) ,
  “ (retval_3 >= 0) ” 
  &&  “ (retval_3 <= 0) ” 
  &&  “ ((Zabs (n)) = (Zabs (m))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) 0 )
.

Definition mpz_abs_sub_return_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= bn) ” 
  &&  “ ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m)) - (Zabs (n)) )) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (m)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (n)) an ) ” 
  &&  “ (cmp < 0) ” 
  &&  “ (cmp <= 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z_compact UINT_MOD rp val_r_out retval )
  **  (UIntArray.undef_seg rp retval bn )
  **  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) (-retval) )
.

Definition mpz_abs_sub_return_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= an) ” 
  &&  “ ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n)) - (Zabs (m)) )) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (m)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (n)) an ) ” 
  &&  “ (cmp > 0) ” 
  &&  “ ((Zabs (n)) > (Zabs (m))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z_compact UINT_MOD rp val_r_out retval )
  **  (UIntArray.undef_seg rp retval an )
  **  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
.

Definition mpz_abs_sub_partial_solve_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) ,
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  EX (cap: Z)  (size: Z)  (ptr: Z) ,
  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
.

Definition mpz_abs_sub_partial_solve_wit_2_pure := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) ,
  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ”
.

Definition mpz_abs_sub_partial_solve_wit_2_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) ,
  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
.

Definition mpz_abs_sub_partial_solve_wit_2 := mpz_abs_sub_partial_solve_wit_2_pure -> mpz_abs_sub_partial_solve_wit_2_aux.

Definition mpz_abs_sub_partial_solve_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) ,
  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  EX (cap_2: Z)  (size_2: Z)  (ptr_2: Z) ,
  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
.

Definition mpz_abs_sub_partial_solve_wit_4_pure := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size_2: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size: Z) (cap_2: Z) ,
  “ (same_sign m size ) ” 
  &&  “ ((Zabs (size)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size_2))) ” 
  &&  “ (same_sign n size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |->_)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_2)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ”
.

Definition mpz_abs_sub_partial_solve_wit_4_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size_2: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size: Z) (cap_2: Z) ,
  “ (same_sign m size ) ” 
  &&  “ ((Zabs (size)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size_2))) ” 
  &&  “ (same_sign n size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_2)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ” 
  &&  “ (same_sign m size ) ” 
  &&  “ ((Zabs (size)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size_2))) ” 
  &&  “ (same_sign n size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_2)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
.

Definition mpz_abs_sub_partial_solve_wit_4 := mpz_abs_sub_partial_solve_wit_4_pure -> mpz_abs_sub_partial_solve_wit_4_aux.

Definition mpz_abs_sub_partial_solve_wit_5_pure := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) ,
  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (retval >= 0) ” 
  &&  “ (retval_2 >= 0) ” 
  &&  “ ((Zabs (size_2)) >= 0) ” 
  &&  “ ((Zabs (size)) >= 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_5_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) ,
  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  “ (retval >= 0) ” 
  &&  “ (retval_2 >= 0) ” 
  &&  “ ((Zabs (size_2)) >= 0) ” 
  &&  “ ((Zabs (size)) >= 0) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
.

Definition mpz_abs_sub_partial_solve_wit_5 := mpz_abs_sub_partial_solve_wit_5_pure -> mpz_abs_sub_partial_solve_wit_5_aux.

Definition mpz_abs_sub_partial_solve_wit_6_pure := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rptr: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) ,
  “ (cmp > 0) ” 
  &&  “ ((Zabs (n)) > (Zabs (m))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (rcap >= 0) ”
  &&  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (rcap >= 0) ” 
  &&  “ (an >= 1) ” 
  &&  “ (an <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= INT_MAX) ” 
  &&  “ ((Zabs (a_pre__mp_size)) >= 1) ” 
  &&  “ (rcap <= INT_MAX) ”
.

Definition mpz_abs_sub_partial_solve_wit_6_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rptr: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) ,
  “ (cmp > 0) ” 
  &&  “ ((Zabs (n)) > (Zabs (m))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (rcap >= 0) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
|--
  “ (rcap >= 0) ” 
  &&  “ (an >= 1) ” 
  &&  “ (an <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= INT_MAX) ” 
  &&  “ ((Zabs (a_pre__mp_size)) >= 1) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ (cmp > 0) ” 
  &&  “ ((Zabs (n)) > (Zabs (m))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (rcap >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
.

Definition mpz_abs_sub_partial_solve_wit_6 := mpz_abs_sub_partial_solve_wit_6_pure -> mpz_abs_sub_partial_solve_wit_6_aux.

Definition mpz_abs_sub_partial_solve_wit_7_pure := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) ,
  “ (cmp > 0) ” 
  &&  “ ((Zabs (n)) > (Zabs (m))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (an >= bn) ” 
  &&  “ (an > 0) ” 
  &&  “ (bn >= 0) ” 
  &&  “ ((Zabs (b_pre__mp_size)) >= 0) ” 
  &&  “ ((Zabs (a_pre__mp_size)) > 0) ” 
  &&  “ ((Zabs (a_pre__mp_size)) >= (Zabs (b_pre__mp_size))) ”
.

Definition mpz_abs_sub_partial_solve_wit_7_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) ,
  “ (cmp > 0) ” 
  &&  “ ((Zabs (n)) > (Zabs (m))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (an >= bn) ” 
  &&  “ (an > 0) ” 
  &&  “ (bn >= 0) ” 
  &&  “ ((Zabs (b_pre__mp_size)) >= 0) ” 
  &&  “ ((Zabs (a_pre__mp_size)) > 0) ” 
  &&  “ ((Zabs (a_pre__mp_size)) >= (Zabs (b_pre__mp_size))) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (m)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (n)) an ) ” 
  &&  “ (cmp > 0) ” 
  &&  “ ((Zabs (n)) > (Zabs (m))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_full rp an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
.

Definition mpz_abs_sub_partial_solve_wit_7 := mpz_abs_sub_partial_solve_wit_7_pure -> mpz_abs_sub_partial_solve_wit_7_aux.

Definition mpz_abs_sub_partial_solve_wit_8_pure := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval: Z) ,
  “ ((val_r_out - (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n)) - (Zabs (m)) )) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (m)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (n)) an ) ” 
  &&  “ (cmp > 0) ” 
  &&  “ ((Zabs (n)) > (Zabs (m))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD rp val_r_out an )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (0 <= an) ” 
  &&  “ (0 <= (Zabs (a_pre__mp_size))) ”
.

Definition mpz_abs_sub_partial_solve_wit_8_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval: Z) ,
  “ ((val_r_out - (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n)) - (Zabs (m)) )) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (m)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (n)) an ) ” 
  &&  “ (cmp > 0) ” 
  &&  “ ((Zabs (n)) > (Zabs (m))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD rp val_r_out an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (0 <= an) ” 
  &&  “ (0 <= (Zabs (a_pre__mp_size))) ” 
  &&  “ ((val_r_out - (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n)) - (Zabs (m)) )) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (m)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (n)) an ) ” 
  &&  “ (cmp > 0) ” 
  &&  “ ((Zabs (n)) > (Zabs (m))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z UINT_MOD rp val_r_out an )
  **  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
.

Definition mpz_abs_sub_partial_solve_wit_8 := mpz_abs_sub_partial_solve_wit_8_pure -> mpz_abs_sub_partial_solve_wit_8_aux.

Definition mpz_abs_sub_partial_solve_wit_9_pure := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rptr: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) ,
  “ (cmp < 0) ” 
  &&  “ (cmp <= 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (rcap >= 0) ”
  &&  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (rcap >= 0) ” 
  &&  “ (bn >= 1) ” 
  &&  “ (bn <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= INT_MAX) ” 
  &&  “ ((Zabs (b_pre__mp_size)) >= 1) ” 
  &&  “ (rcap <= INT_MAX) ”
.

Definition mpz_abs_sub_partial_solve_wit_9_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rptr: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) ,
  “ (cmp < 0) ” 
  &&  “ (cmp <= 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (rcap >= 0) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
|--
  “ (rcap >= 0) ” 
  &&  “ (bn >= 1) ” 
  &&  “ (bn <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= INT_MAX) ” 
  &&  “ ((Zabs (b_pre__mp_size)) >= 1) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ (cmp < 0) ” 
  &&  “ (cmp <= 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (rcap >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
.

Definition mpz_abs_sub_partial_solve_wit_9 := mpz_abs_sub_partial_solve_wit_9_pure -> mpz_abs_sub_partial_solve_wit_9_aux.

Definition mpz_abs_sub_partial_solve_wit_10_pure := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) ,
  “ (cmp < 0) ” 
  &&  “ (cmp <= 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap))) ”
  &&  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (bn >= an) ” 
  &&  “ (bn > 0) ” 
  &&  “ (an >= 0) ” 
  &&  “ ((Zabs (a_pre__mp_size)) >= 0) ” 
  &&  “ ((Zabs (b_pre__mp_size)) > 0) ” 
  &&  “ ((Zabs (b_pre__mp_size)) >= (Zabs (a_pre__mp_size))) ”
.

Definition mpz_abs_sub_partial_solve_wit_10_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) ,
  “ (cmp < 0) ” 
  &&  “ (cmp <= 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap))) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (bn >= an) ” 
  &&  “ (bn > 0) ” 
  &&  “ (an >= 0) ” 
  &&  “ ((Zabs (a_pre__mp_size)) >= 0) ” 
  &&  “ ((Zabs (b_pre__mp_size)) > 0) ” 
  &&  “ ((Zabs (b_pre__mp_size)) >= (Zabs (a_pre__mp_size))) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (m)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (n)) an ) ” 
  &&  “ (cmp < 0) ” 
  &&  “ (cmp <= 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (UIntArray.undef_full rp bn )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
.

Definition mpz_abs_sub_partial_solve_wit_10 := mpz_abs_sub_partial_solve_wit_10_pure -> mpz_abs_sub_partial_solve_wit_10_aux.

Definition mpz_abs_sub_partial_solve_wit_11_pure := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval: Z) ,
  “ ((val_r_out - (retval * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m)) - (Zabs (n)) )) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (m)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (n)) an ) ” 
  &&  “ (cmp < 0) ” 
  &&  “ (cmp <= 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (mpd_store_Z UINT_MOD rp val_r_out bn )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (0 <= bn) ” 
  &&  “ (0 <= (Zabs (b_pre__mp_size))) ”
.

Definition mpz_abs_sub_partial_solve_wit_11_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval: Z) ,
  “ ((val_r_out - (retval * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m)) - (Zabs (n)) )) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (m)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (n)) an ) ” 
  &&  “ (cmp < 0) ” 
  &&  “ (cmp <= 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (mpd_store_Z UINT_MOD rp val_r_out bn )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (0 <= bn) ” 
  &&  “ (0 <= (Zabs (b_pre__mp_size))) ” 
  &&  “ ((val_r_out - (retval * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m)) - (Zabs (n)) )) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (m)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (n)) an ) ” 
  &&  “ (cmp < 0) ” 
  &&  “ (cmp <= 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z UINT_MOD rp val_r_out bn )
  **  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
.

Definition mpz_abs_sub_partial_solve_wit_11 := mpz_abs_sub_partial_solve_wit_11_pure -> mpz_abs_sub_partial_solve_wit_11_aux.

(*----- Function mpz_add -----*)

Definition mpz_add_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) ,
  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_add_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) ,
  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_add_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) ,
  “ (size_3 < 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (retval <> (INT_MIN)) ”
.

Definition mpz_add_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) ,
  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_add_safety_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) ,
  “ (size_3 < 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (retval <> (INT_MIN)) ”
.

Definition mpz_add_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) ,
  “ (same_sign ((Zabs (n)) - (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 >= 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> retval)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre (n + m ) )
.

Definition mpz_add_return_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) ,
  “ (same_sign ((Zabs (n)) - (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 < 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-retval))
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre (n + m ) )
.

Definition mpz_add_return_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) ,
  “ (same_sign ((Zabs (n)) + (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 >= 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> retval)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre (n + m ) )
.

Definition mpz_add_return_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) ,
  “ (same_sign ((Zabs (n)) + (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 < 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-retval))
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre (n + m ) )
.

Definition mpz_add_partial_solve_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) ,
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  EX (cap: Z)  (size: Z)  (ptr: Z) ,
  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
.

Definition mpz_add_partial_solve_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) ,
  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  EX (cap_2: Z)  (size_2: Z)  (ptr_2: Z) ,
  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
.

Definition mpz_add_partial_solve_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) ,
  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
.

Definition mpz_add_partial_solve_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) ,
  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
.

Definition mpz_add_partial_solve_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) ,
  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
|--
  EX (cap_3: Z)  (size_3: Z)  (ptr: Z) ,
  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
.

Definition mpz_add_partial_solve_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) ,
  “ (size_3 >= 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
|--
  EX (cap_4: Z)  (ptr_2: Z) ,
  “ (same_sign ((Zabs (n)) - (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 >= 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
.

Definition mpz_add_partial_solve_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) ,
  “ (size_3 < 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
|--
  EX (cap_4: Z)  (ptr_2: Z) ,
  “ (same_sign ((Zabs (n)) - (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 < 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
.

Definition mpz_add_partial_solve_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) ,
  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
|--
  EX (cap_3: Z)  (size_3: Z)  (ptr: Z) ,
  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
.

Definition mpz_add_partial_solve_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) ,
  “ (size_3 >= 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
|--
  EX (cap_4: Z)  (ptr_2: Z) ,
  “ (same_sign ((Zabs (n)) + (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 >= 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
.

Definition mpz_add_partial_solve_wit_10 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) ,
  “ (size_3 < 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
|--
  EX (cap_4: Z)  (ptr_2: Z) ,
  “ (same_sign ((Zabs (n)) + (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 < 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
.

(*----- Function mpz_sub -----*)

Definition mpz_sub_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) ,
  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_sub_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) ,
  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_sub_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) ,
  “ (size_3 < 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (retval <> (INT_MIN)) ”
.

Definition mpz_sub_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) ,
  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_sub_safety_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) ,
  “ (size_3 < 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (retval <> (INT_MIN)) ”
.

Definition mpz_sub_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) ,
  “ (same_sign ((Zabs (n)) + (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 >= 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> retval)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre (n - m ) )
.

Definition mpz_sub_return_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) ,
  “ (same_sign ((Zabs (n)) + (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 < 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-retval))
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre (n - m ) )
.

Definition mpz_sub_return_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) ,
  “ (same_sign ((Zabs (n)) - (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 >= 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> retval)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre (n - m ) )
.

Definition mpz_sub_return_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) ,
  “ (same_sign ((Zabs (n)) - (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 < 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-retval))
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre (n - m ) )
.

Definition mpz_sub_partial_solve_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) ,
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  EX (cap: Z)  (size: Z)  (ptr: Z) ,
  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
.

Definition mpz_sub_partial_solve_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) ,
  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  EX (cap_2: Z)  (size_2: Z)  (ptr_2: Z) ,
  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
.

Definition mpz_sub_partial_solve_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) ,
  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
.

Definition mpz_sub_partial_solve_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) ,
  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
.

Definition mpz_sub_partial_solve_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) ,
  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
|--
  EX (cap_3: Z)  (size_3: Z)  (ptr: Z) ,
  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
.

Definition mpz_sub_partial_solve_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) ,
  “ (size_3 >= 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
|--
  EX (cap_4: Z)  (ptr_2: Z) ,
  “ (same_sign ((Zabs (n)) + (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 >= 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
.

Definition mpz_sub_partial_solve_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) ,
  “ (size_3 < 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
|--
  EX (cap_4: Z)  (ptr_2: Z) ,
  “ (same_sign ((Zabs (n)) + (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 < 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
.

Definition mpz_sub_partial_solve_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) ,
  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
|--
  EX (cap_3: Z)  (size_3: Z)  (ptr: Z) ,
  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
.

Definition mpz_sub_partial_solve_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) ,
  “ (size_3 >= 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
|--
  EX (cap_4: Z)  (ptr_2: Z) ,
  “ (same_sign ((Zabs (n)) - (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 >= 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
.

Definition mpz_sub_partial_solve_wit_10 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) ,
  “ (size_3 < 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
|--
  EX (cap_4: Z)  (ptr_2: Z) ,
  “ (same_sign ((Zabs (n)) - (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 < 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.

Axiom proof_of_gmp_abs_safety_wit_1 : gmp_abs_safety_wit_1.
Axiom proof_of_gmp_abs_safety_wit_2 : gmp_abs_safety_wit_2.
Axiom proof_of_gmp_abs_return_wit_1 : gmp_abs_return_wit_1.
Axiom proof_of_gmp_abs_return_wit_2 : gmp_abs_return_wit_2.
Axiom proof_of_gmp_max_return_wit_1 : gmp_max_return_wit_1.
Axiom proof_of_gmp_max_return_wit_2 : gmp_max_return_wit_2.
Axiom proof_of_gmp_cmp_safety_wit_1 : gmp_cmp_safety_wit_1.
Axiom proof_of_gmp_cmp_safety_wit_2 : gmp_cmp_safety_wit_2.
Axiom proof_of_gmp_cmp_safety_wit_3 : gmp_cmp_safety_wit_3.
Axiom proof_of_gmp_cmp_safety_wit_4 : gmp_cmp_safety_wit_4.
Axiom proof_of_gmp_cmp_return_wit_1 : gmp_cmp_return_wit_1.
Axiom proof_of_gmp_cmp_return_wit_2 : gmp_cmp_return_wit_2.
Axiom proof_of_gmp_cmp_return_wit_3 : gmp_cmp_return_wit_3.
Axiom proof_of_mpn_copyi_safety_wit_1 : mpn_copyi_safety_wit_1.
Axiom proof_of_mpn_copyi_safety_wit_2 : mpn_copyi_safety_wit_2.
Axiom proof_of_mpn_copyi_entail_wit_1 : mpn_copyi_entail_wit_1.
Axiom proof_of_mpn_copyi_entail_wit_2 : mpn_copyi_entail_wit_2.
Axiom proof_of_mpn_copyi_return_wit_1 : mpn_copyi_return_wit_1.
Axiom proof_of_mpn_copyi_partial_solve_wit_1 : mpn_copyi_partial_solve_wit_1.
Axiom proof_of_mpn_copyi_partial_solve_wit_2 : mpn_copyi_partial_solve_wit_2.
Axiom proof_of_mpn_copyi_partial_solve_wit_3 : mpn_copyi_partial_solve_wit_3.
Axiom proof_of_mpn_copyi_which_implies_wit_1 : mpn_copyi_which_implies_wit_1.
Axiom proof_of_mpn_cmp_safety_wit_1 : mpn_cmp_safety_wit_1.
Axiom proof_of_mpn_cmp_safety_wit_2 : mpn_cmp_safety_wit_2.
Axiom proof_of_mpn_cmp_safety_wit_3 : mpn_cmp_safety_wit_3.
Axiom proof_of_mpn_cmp_safety_wit_4 : mpn_cmp_safety_wit_4.
Axiom proof_of_mpn_cmp_safety_wit_5 : mpn_cmp_safety_wit_5.
Axiom proof_of_mpn_cmp_safety_wit_6 : mpn_cmp_safety_wit_6.
Axiom proof_of_mpn_cmp_safety_wit_7 : mpn_cmp_safety_wit_7.
Axiom proof_of_mpn_cmp_entail_wit_1 : mpn_cmp_entail_wit_1.
Axiom proof_of_mpn_cmp_entail_wit_2 : mpn_cmp_entail_wit_2.
Axiom proof_of_mpn_cmp_return_wit_1 : mpn_cmp_return_wit_1.
Axiom proof_of_mpn_cmp_return_wit_2 : mpn_cmp_return_wit_2.
Axiom proof_of_mpn_cmp_return_wit_3 : mpn_cmp_return_wit_3.
Axiom proof_of_mpn_cmp_partial_solve_wit_1 : mpn_cmp_partial_solve_wit_1.
Axiom proof_of_mpn_cmp_partial_solve_wit_2 : mpn_cmp_partial_solve_wit_2.
Axiom proof_of_mpn_cmp_partial_solve_wit_3 : mpn_cmp_partial_solve_wit_3.
Axiom proof_of_mpn_cmp_partial_solve_wit_4 : mpn_cmp_partial_solve_wit_4.
Axiom proof_of_mpn_cmp_partial_solve_wit_5 : mpn_cmp_partial_solve_wit_5.
Axiom proof_of_mpn_cmp_which_implies_wit_1 : mpn_cmp_which_implies_wit_1.
Axiom proof_of_mpn_cmp4_safety_wit_1 : mpn_cmp4_safety_wit_1.
Axiom proof_of_mpn_cmp4_safety_wit_2 : mpn_cmp4_safety_wit_2.
Axiom proof_of_mpn_cmp4_safety_wit_3 : mpn_cmp4_safety_wit_3.
Axiom proof_of_mpn_cmp4_return_wit_1 : mpn_cmp4_return_wit_1.
Axiom proof_of_mpn_cmp4_return_wit_2 : mpn_cmp4_return_wit_2.
Axiom proof_of_mpn_cmp4_return_wit_3 : mpn_cmp4_return_wit_3.
Axiom proof_of_mpn_cmp4_return_wit_4 : mpn_cmp4_return_wit_4.
Axiom proof_of_mpn_cmp4_return_wit_5 : mpn_cmp4_return_wit_5.
Axiom proof_of_mpn_cmp4_partial_solve_wit_1_pure : mpn_cmp4_partial_solve_wit_1_pure.
Axiom proof_of_mpn_cmp4_partial_solve_wit_1 : mpn_cmp4_partial_solve_wit_1.
Axiom proof_of_mpn_normalized_size_safety_wit_1 : mpn_normalized_size_safety_wit_1.
Axiom proof_of_mpn_normalized_size_safety_wit_2 : mpn_normalized_size_safety_wit_2.
Axiom proof_of_mpn_normalized_size_safety_wit_3 : mpn_normalized_size_safety_wit_3.
Axiom proof_of_mpn_normalized_size_safety_wit_4 : mpn_normalized_size_safety_wit_4.
Axiom proof_of_mpn_normalized_size_safety_wit_5 : mpn_normalized_size_safety_wit_5.
Axiom proof_of_mpn_normalized_size_entail_wit_1 : mpn_normalized_size_entail_wit_1.
Axiom proof_of_mpn_normalized_size_entail_wit_2 : mpn_normalized_size_entail_wit_2.
Axiom proof_of_mpn_normalized_size_entail_wit_3 : mpn_normalized_size_entail_wit_3.
Axiom proof_of_mpn_normalized_size_return_wit_1 : mpn_normalized_size_return_wit_1.
Axiom proof_of_mpn_normalized_size_return_wit_2 : mpn_normalized_size_return_wit_2.
Axiom proof_of_mpn_normalized_size_partial_solve_wit_1 : mpn_normalized_size_partial_solve_wit_1.
Axiom proof_of_mpn_normalized_size_partial_solve_wit_2 : mpn_normalized_size_partial_solve_wit_2.
Axiom proof_of_mpn_normalized_size_which_implies_wit_1 : mpn_normalized_size_which_implies_wit_1.
Axiom proof_of_mpn_add_1_safety_wit_1 : mpn_add_1_safety_wit_1.
Axiom proof_of_mpn_add_1_safety_wit_2 : mpn_add_1_safety_wit_2.
Axiom proof_of_mpn_add_1_safety_wit_3 : mpn_add_1_safety_wit_3.
Axiom proof_of_mpn_add_1_safety_wit_4 : mpn_add_1_safety_wit_4.
Axiom proof_of_mpn_add_1_safety_wit_5 : mpn_add_1_safety_wit_5.
Axiom proof_of_mpn_add_1_entail_wit_1_1 : mpn_add_1_entail_wit_1_1.
Axiom proof_of_mpn_add_1_entail_wit_1_2 : mpn_add_1_entail_wit_1_2.
Axiom proof_of_mpn_add_1_entail_wit_2_1 : mpn_add_1_entail_wit_2_1.
Axiom proof_of_mpn_add_1_entail_wit_2_2 : mpn_add_1_entail_wit_2_2.
Axiom proof_of_mpn_add_1_return_wit_1 : mpn_add_1_return_wit_1.
Axiom proof_of_mpn_add_1_partial_solve_wit_1 : mpn_add_1_partial_solve_wit_1.
Axiom proof_of_mpn_add_1_partial_solve_wit_2 : mpn_add_1_partial_solve_wit_2.
Axiom proof_of_mpn_add_1_partial_solve_wit_3 : mpn_add_1_partial_solve_wit_3.
Axiom proof_of_mpn_add_1_partial_solve_wit_4 : mpn_add_1_partial_solve_wit_4.
Axiom proof_of_mpn_add_1_partial_solve_wit_5 : mpn_add_1_partial_solve_wit_5.
Axiom proof_of_mpn_add_1_partial_solve_wit_6 : mpn_add_1_partial_solve_wit_6.
Axiom proof_of_mpn_add_1_partial_solve_wit_7 : mpn_add_1_partial_solve_wit_7.
Axiom proof_of_mpn_add_1_which_implies_wit_1 : mpn_add_1_which_implies_wit_1.
Axiom proof_of_mpn_add_n_safety_wit_1 : mpn_add_n_safety_wit_1.
Axiom proof_of_mpn_add_n_safety_wit_2 : mpn_add_n_safety_wit_2.
Axiom proof_of_mpn_add_n_safety_wit_3 : mpn_add_n_safety_wit_3.
Axiom proof_of_mpn_add_n_safety_wit_4 : mpn_add_n_safety_wit_4.
Axiom proof_of_mpn_add_n_safety_wit_5 : mpn_add_n_safety_wit_5.
Axiom proof_of_mpn_add_n_safety_wit_6 : mpn_add_n_safety_wit_6.
Axiom proof_of_mpn_add_n_entail_wit_1 : mpn_add_n_entail_wit_1.
Axiom proof_of_mpn_add_n_entail_wit_2_1 : mpn_add_n_entail_wit_2_1.
Axiom proof_of_mpn_add_n_entail_wit_2_2 : mpn_add_n_entail_wit_2_2.
Axiom proof_of_mpn_add_n_entail_wit_2_3 : mpn_add_n_entail_wit_2_3.
Axiom proof_of_mpn_add_n_entail_wit_2_4 : mpn_add_n_entail_wit_2_4.
Axiom proof_of_mpn_add_n_return_wit_1 : mpn_add_n_return_wit_1.
Axiom proof_of_mpn_add_n_partial_solve_wit_1 : mpn_add_n_partial_solve_wit_1.
Axiom proof_of_mpn_add_n_partial_solve_wit_2 : mpn_add_n_partial_solve_wit_2.
Axiom proof_of_mpn_add_n_partial_solve_wit_3 : mpn_add_n_partial_solve_wit_3.
Axiom proof_of_mpn_add_n_partial_solve_wit_4 : mpn_add_n_partial_solve_wit_4.
Axiom proof_of_mpn_add_n_partial_solve_wit_5 : mpn_add_n_partial_solve_wit_5.
Axiom proof_of_mpn_add_n_partial_solve_wit_6 : mpn_add_n_partial_solve_wit_6.
Axiom proof_of_mpn_add_n_partial_solve_wit_7 : mpn_add_n_partial_solve_wit_7.
Axiom proof_of_mpn_add_n_which_implies_wit_1 : mpn_add_n_which_implies_wit_1.
Axiom proof_of_mpn_add_safety_wit_1 : mpn_add_safety_wit_1.
Axiom proof_of_mpn_add_entail_wit_1 : mpn_add_entail_wit_1.
Axiom proof_of_mpn_add_return_wit_1 : mpn_add_return_wit_1.
Axiom proof_of_mpn_add_return_wit_2 : mpn_add_return_wit_2.
Axiom proof_of_mpn_add_partial_solve_wit_1_pure : mpn_add_partial_solve_wit_1_pure.
Axiom proof_of_mpn_add_partial_solve_wit_1 : mpn_add_partial_solve_wit_1.
Axiom proof_of_mpn_add_partial_solve_wit_2_pure : mpn_add_partial_solve_wit_2_pure.
Axiom proof_of_mpn_add_partial_solve_wit_2 : mpn_add_partial_solve_wit_2.
Axiom proof_of_mpn_add_partial_solve_wit_3_pure : mpn_add_partial_solve_wit_3_pure.
Axiom proof_of_mpn_add_partial_solve_wit_3 : mpn_add_partial_solve_wit_3.
Axiom proof_of_mpn_add_partial_solve_wit_4 : mpn_add_partial_solve_wit_4.
Axiom proof_of_mpn_add_partial_solve_wit_5_pure : mpn_add_partial_solve_wit_5_pure.
Axiom proof_of_mpn_add_partial_solve_wit_5 : mpn_add_partial_solve_wit_5.
Axiom proof_of_mpn_add_which_implies_wit_1 : mpn_add_which_implies_wit_1.
Axiom proof_of_mpn_add_which_implies_wit_2 : mpn_add_which_implies_wit_2.
Axiom proof_of_mpn_add_which_implies_wit_3 : mpn_add_which_implies_wit_3.
Axiom proof_of_gmp_umul_ppmm_safety_wit_1 : gmp_umul_ppmm_safety_wit_1.
Axiom proof_of_gmp_umul_ppmm_safety_wit_2 : gmp_umul_ppmm_safety_wit_2.
Axiom proof_of_gmp_umul_ppmm_safety_wit_3 : gmp_umul_ppmm_safety_wit_3.
Axiom proof_of_gmp_umul_ppmm_safety_wit_4 : gmp_umul_ppmm_safety_wit_4.
Axiom proof_of_gmp_umul_ppmm_safety_wit_5 : gmp_umul_ppmm_safety_wit_5.
Axiom proof_of_gmp_umul_ppmm_safety_wit_6 : gmp_umul_ppmm_safety_wit_6.
Axiom proof_of_gmp_umul_ppmm_safety_wit_7 : gmp_umul_ppmm_safety_wit_7.
Axiom proof_of_gmp_umul_ppmm_safety_wit_8 : gmp_umul_ppmm_safety_wit_8.
Axiom proof_of_gmp_umul_ppmm_safety_wit_9 : gmp_umul_ppmm_safety_wit_9.
Axiom proof_of_gmp_umul_ppmm_safety_wit_10 : gmp_umul_ppmm_safety_wit_10.
Axiom proof_of_gmp_umul_ppmm_safety_wit_11 : gmp_umul_ppmm_safety_wit_11.
Axiom proof_of_gmp_umul_ppmm_safety_wit_12 : gmp_umul_ppmm_safety_wit_12.
Axiom proof_of_gmp_umul_ppmm_safety_wit_13 : gmp_umul_ppmm_safety_wit_13.
Axiom proof_of_gmp_umul_ppmm_safety_wit_14 : gmp_umul_ppmm_safety_wit_14.
Axiom proof_of_gmp_umul_ppmm_safety_wit_15 : gmp_umul_ppmm_safety_wit_15.
Axiom proof_of_gmp_umul_ppmm_safety_wit_16 : gmp_umul_ppmm_safety_wit_16.
Axiom proof_of_gmp_umul_ppmm_safety_wit_17 : gmp_umul_ppmm_safety_wit_17.
Axiom proof_of_gmp_umul_ppmm_safety_wit_18 : gmp_umul_ppmm_safety_wit_18.
Axiom proof_of_gmp_umul_ppmm_safety_wit_19 : gmp_umul_ppmm_safety_wit_19.
Axiom proof_of_gmp_umul_ppmm_entail_wit_1 : gmp_umul_ppmm_entail_wit_1.
Axiom proof_of_gmp_umul_ppmm_entail_wit_2 : gmp_umul_ppmm_entail_wit_2.
Axiom proof_of_gmp_umul_ppmm_return_wit_1 : gmp_umul_ppmm_return_wit_1.
Axiom proof_of_gmp_umul_ppmm_return_wit_2 : gmp_umul_ppmm_return_wit_2.
Axiom proof_of_mpn_mul_1_safety_wit_1 : mpn_mul_1_safety_wit_1.
Axiom proof_of_mpn_mul_1_safety_wit_2 : mpn_mul_1_safety_wit_2.
Axiom proof_of_mpn_mul_1_safety_wit_3 : mpn_mul_1_safety_wit_3.
Axiom proof_of_mpn_mul_1_safety_wit_4 : mpn_mul_1_safety_wit_4.
Axiom proof_of_mpn_mul_1_safety_wit_5 : mpn_mul_1_safety_wit_5.
Axiom proof_of_mpn_mul_1_safety_wit_6 : mpn_mul_1_safety_wit_6.
Axiom proof_of_mpn_mul_1_entail_wit_1 : mpn_mul_1_entail_wit_1.
Axiom proof_of_mpn_mul_1_entail_wit_2 : mpn_mul_1_entail_wit_2.
Axiom proof_of_mpn_mul_1_entail_wit_3 : mpn_mul_1_entail_wit_3.
Axiom proof_of_mpn_mul_1_entail_wit_4 : mpn_mul_1_entail_wit_4.
Axiom proof_of_mpn_mul_1_entail_wit_5_1 : mpn_mul_1_entail_wit_5_1.
Axiom proof_of_mpn_mul_1_entail_wit_5_2 : mpn_mul_1_entail_wit_5_2.
Axiom proof_of_mpn_mul_1_return_wit_1 : mpn_mul_1_return_wit_1.
Axiom proof_of_mpn_mul_1_partial_solve_wit_1 : mpn_mul_1_partial_solve_wit_1.
Axiom proof_of_mpn_mul_1_partial_solve_wit_2 : mpn_mul_1_partial_solve_wit_2.
Axiom proof_of_mpn_mul_1_partial_solve_wit_3 : mpn_mul_1_partial_solve_wit_3.
Axiom proof_of_mpn_mul_1_partial_solve_wit_4 : mpn_mul_1_partial_solve_wit_4.
Axiom proof_of_mpn_sub_1_safety_wit_1 : mpn_sub_1_safety_wit_1.
Axiom proof_of_mpn_sub_1_safety_wit_2 : mpn_sub_1_safety_wit_2.
Axiom proof_of_mpn_sub_1_safety_wit_3 : mpn_sub_1_safety_wit_3.
Axiom proof_of_mpn_sub_1_safety_wit_4 : mpn_sub_1_safety_wit_4.
Axiom proof_of_mpn_sub_1_safety_wit_5 : mpn_sub_1_safety_wit_5.
Axiom proof_of_mpn_sub_1_entail_wit_1_1 : mpn_sub_1_entail_wit_1_1.
Axiom proof_of_mpn_sub_1_entail_wit_1_2 : mpn_sub_1_entail_wit_1_2.
Axiom proof_of_mpn_sub_1_entail_wit_2_1 : mpn_sub_1_entail_wit_2_1.
Axiom proof_of_mpn_sub_1_entail_wit_2_2 : mpn_sub_1_entail_wit_2_2.
Axiom proof_of_mpn_sub_1_return_wit_1 : mpn_sub_1_return_wit_1.
Axiom proof_of_mpn_sub_1_partial_solve_wit_1 : mpn_sub_1_partial_solve_wit_1.
Axiom proof_of_mpn_sub_1_partial_solve_wit_2 : mpn_sub_1_partial_solve_wit_2.
Axiom proof_of_mpn_sub_1_partial_solve_wit_3 : mpn_sub_1_partial_solve_wit_3.
Axiom proof_of_mpn_sub_1_partial_solve_wit_4 : mpn_sub_1_partial_solve_wit_4.
Axiom proof_of_mpn_sub_1_partial_solve_wit_5 : mpn_sub_1_partial_solve_wit_5.
Axiom proof_of_mpn_sub_1_partial_solve_wit_6 : mpn_sub_1_partial_solve_wit_6.
Axiom proof_of_mpn_sub_1_partial_solve_wit_7 : mpn_sub_1_partial_solve_wit_7.
Axiom proof_of_mpn_sub_1_which_implies_wit_1 : mpn_sub_1_which_implies_wit_1.
Axiom proof_of_mpn_sub_n_safety_wit_1 : mpn_sub_n_safety_wit_1.
Axiom proof_of_mpn_sub_n_safety_wit_2 : mpn_sub_n_safety_wit_2.
Axiom proof_of_mpn_sub_n_safety_wit_3 : mpn_sub_n_safety_wit_3.
Axiom proof_of_mpn_sub_n_safety_wit_4 : mpn_sub_n_safety_wit_4.
Axiom proof_of_mpn_sub_n_safety_wit_5 : mpn_sub_n_safety_wit_5.
Axiom proof_of_mpn_sub_n_safety_wit_6 : mpn_sub_n_safety_wit_6.
Axiom proof_of_mpn_sub_n_entail_wit_1 : mpn_sub_n_entail_wit_1.
Axiom proof_of_mpn_sub_n_entail_wit_2_1 : mpn_sub_n_entail_wit_2_1.
Axiom proof_of_mpn_sub_n_entail_wit_2_2 : mpn_sub_n_entail_wit_2_2.
Axiom proof_of_mpn_sub_n_entail_wit_2_3 : mpn_sub_n_entail_wit_2_3.
Axiom proof_of_mpn_sub_n_entail_wit_2_4 : mpn_sub_n_entail_wit_2_4.
Axiom proof_of_mpn_sub_n_return_wit_1 : mpn_sub_n_return_wit_1.
Axiom proof_of_mpn_sub_n_partial_solve_wit_1 : mpn_sub_n_partial_solve_wit_1.
Axiom proof_of_mpn_sub_n_partial_solve_wit_2 : mpn_sub_n_partial_solve_wit_2.
Axiom proof_of_mpn_sub_n_partial_solve_wit_3 : mpn_sub_n_partial_solve_wit_3.
Axiom proof_of_mpn_sub_n_partial_solve_wit_4 : mpn_sub_n_partial_solve_wit_4.
Axiom proof_of_mpn_sub_n_partial_solve_wit_5 : mpn_sub_n_partial_solve_wit_5.
Axiom proof_of_mpn_sub_n_partial_solve_wit_6 : mpn_sub_n_partial_solve_wit_6.
Axiom proof_of_mpn_sub_n_partial_solve_wit_7 : mpn_sub_n_partial_solve_wit_7.
Axiom proof_of_mpn_sub_n_which_implies_wit_1 : mpn_sub_n_which_implies_wit_1.
Axiom proof_of_mpn_sub_safety_wit_1 : mpn_sub_safety_wit_1.
Axiom proof_of_mpn_sub_entail_wit_1 : mpn_sub_entail_wit_1.
Axiom proof_of_mpn_sub_entail_wit_2 : mpn_sub_entail_wit_2.
Axiom proof_of_mpn_sub_return_wit_1 : mpn_sub_return_wit_1.
Axiom proof_of_mpn_sub_return_wit_2 : mpn_sub_return_wit_2.
Axiom proof_of_mpn_sub_partial_solve_wit_1_pure : mpn_sub_partial_solve_wit_1_pure.
Axiom proof_of_mpn_sub_partial_solve_wit_1 : mpn_sub_partial_solve_wit_1.
Axiom proof_of_mpn_sub_partial_solve_wit_2_pure : mpn_sub_partial_solve_wit_2_pure.
Axiom proof_of_mpn_sub_partial_solve_wit_2 : mpn_sub_partial_solve_wit_2.
Axiom proof_of_mpn_sub_partial_solve_wit_3_pure : mpn_sub_partial_solve_wit_3_pure.
Axiom proof_of_mpn_sub_partial_solve_wit_3 : mpn_sub_partial_solve_wit_3.
Axiom proof_of_mpn_sub_partial_solve_wit_4 : mpn_sub_partial_solve_wit_4.
Axiom proof_of_mpn_sub_partial_solve_wit_5_pure : mpn_sub_partial_solve_wit_5_pure.
Axiom proof_of_mpn_sub_partial_solve_wit_5 : mpn_sub_partial_solve_wit_5.
Axiom proof_of_mpn_sub_which_implies_wit_1 : mpn_sub_which_implies_wit_1.
Axiom proof_of_mpn_sub_which_implies_wit_2 : mpn_sub_which_implies_wit_2.
Axiom proof_of_mpn_sub_which_implies_wit_3 : mpn_sub_which_implies_wit_3.
Axiom proof_of_mpz_clear_return_wit_1 : mpz_clear_return_wit_1.
Axiom proof_of_mpz_clear_return_wit_2 : mpz_clear_return_wit_2.
Axiom proof_of_mpz_clear_partial_solve_wit_1 : mpz_clear_partial_solve_wit_1.
Axiom proof_of_mpz_clear_partial_solve_wit_2 : mpz_clear_partial_solve_wit_2.
Axiom proof_of_mpz_realloc_safety_wit_1 : mpz_realloc_safety_wit_1.
Axiom proof_of_mpz_realloc_safety_wit_2 : mpz_realloc_safety_wit_2.
Axiom proof_of_mpz_realloc_safety_wit_3 : mpz_realloc_safety_wit_3.
Axiom proof_of_mpz_realloc_return_wit_1 : mpz_realloc_return_wit_1.
Axiom proof_of_mpz_realloc_return_wit_2 : mpz_realloc_return_wit_2.
Axiom proof_of_mpz_realloc_return_wit_3 : mpz_realloc_return_wit_3.
Axiom proof_of_mpz_realloc_return_wit_4 : mpz_realloc_return_wit_4.
Axiom proof_of_mpz_realloc_partial_solve_wit_1 : mpz_realloc_partial_solve_wit_1.
Axiom proof_of_mpz_realloc_partial_solve_wit_2_pure : mpz_realloc_partial_solve_wit_2_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_2 : mpz_realloc_partial_solve_wit_2.
Axiom proof_of_mpz_realloc_partial_solve_wit_3_pure : mpz_realloc_partial_solve_wit_3_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_3 : mpz_realloc_partial_solve_wit_3.
Axiom proof_of_mpz_realloc_partial_solve_wit_4_pure : mpz_realloc_partial_solve_wit_4_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_4 : mpz_realloc_partial_solve_wit_4.
Axiom proof_of_mpz_realloc_partial_solve_wit_5_pure : mpz_realloc_partial_solve_wit_5_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_5 : mpz_realloc_partial_solve_wit_5.
Axiom proof_of_mrz_realloc_if_return_wit_1 : mrz_realloc_if_return_wit_1.
Axiom proof_of_mrz_realloc_if_return_wit_2 : mrz_realloc_if_return_wit_2.
Axiom proof_of_mrz_realloc_if_partial_solve_wit_1_pure : mrz_realloc_if_partial_solve_wit_1_pure.
Axiom proof_of_mrz_realloc_if_partial_solve_wit_1 : mrz_realloc_if_partial_solve_wit_1.
Axiom proof_of_mpz_sgn_safety_wit_1 : mpz_sgn_safety_wit_1.
Axiom proof_of_mpz_sgn_return_wit_1 : mpz_sgn_return_wit_1.
Axiom proof_of_mpz_sgn_return_wit_2 : mpz_sgn_return_wit_2.
Axiom proof_of_mpz_sgn_return_wit_3 : mpz_sgn_return_wit_3.
Axiom proof_of_mpz_sgn_partial_solve_wit_1 : mpz_sgn_partial_solve_wit_1.
Axiom proof_of_mpz_sgn_partial_solve_wit_2 : mpz_sgn_partial_solve_wit_2.
Axiom proof_of_mpz_swap_return_wit_1 : mpz_swap_return_wit_1.
Axiom proof_of_mpz_swap_partial_solve_wit_1 : mpz_swap_partial_solve_wit_1.
Axiom proof_of_mpz_swap_partial_solve_wit_2 : mpz_swap_partial_solve_wit_2.
Axiom proof_of_mpz_swap_partial_solve_wit_3 : mpz_swap_partial_solve_wit_3.
Axiom proof_of_mpz_abs_add_safety_wit_1 : mpz_abs_add_safety_wit_1.
Axiom proof_of_mpz_abs_add_safety_wit_2 : mpz_abs_add_safety_wit_2.
Axiom proof_of_mpz_abs_add_entail_wit_1_1 : mpz_abs_add_entail_wit_1_1.
Axiom proof_of_mpz_abs_add_entail_wit_1_2 : mpz_abs_add_entail_wit_1_2.
Axiom proof_of_mpz_abs_add_entail_wit_2 : mpz_abs_add_entail_wit_2.
Axiom proof_of_mpz_abs_add_return_wit_1 : mpz_abs_add_return_wit_1.
Axiom proof_of_mpz_abs_add_partial_solve_wit_1 : mpz_abs_add_partial_solve_wit_1.
Axiom proof_of_mpz_abs_add_partial_solve_wit_2_pure : mpz_abs_add_partial_solve_wit_2_pure.
Axiom proof_of_mpz_abs_add_partial_solve_wit_2 : mpz_abs_add_partial_solve_wit_2.
Axiom proof_of_mpz_abs_add_partial_solve_wit_3 : mpz_abs_add_partial_solve_wit_3.
Axiom proof_of_mpz_abs_add_partial_solve_wit_4_pure : mpz_abs_add_partial_solve_wit_4_pure.
Axiom proof_of_mpz_abs_add_partial_solve_wit_4 : mpz_abs_add_partial_solve_wit_4.
Axiom proof_of_mpz_abs_add_partial_solve_wit_5 : mpz_abs_add_partial_solve_wit_5.
Axiom proof_of_mpz_abs_add_partial_solve_wit_6 : mpz_abs_add_partial_solve_wit_6.
Axiom proof_of_mpz_abs_add_partial_solve_wit_7_pure : mpz_abs_add_partial_solve_wit_7_pure.
Axiom proof_of_mpz_abs_add_partial_solve_wit_7 : mpz_abs_add_partial_solve_wit_7.
Axiom proof_of_mpz_abs_add_partial_solve_wit_8_pure : mpz_abs_add_partial_solve_wit_8_pure.
Axiom proof_of_mpz_abs_add_partial_solve_wit_8 : mpz_abs_add_partial_solve_wit_8.
Axiom proof_of_mpz_abs_add_partial_solve_wit_9 : mpz_abs_add_partial_solve_wit_9.
Axiom proof_of_mpz_abs_sub_safety_wit_1 : mpz_abs_sub_safety_wit_1.
Axiom proof_of_mpz_abs_sub_safety_wit_2 : mpz_abs_sub_safety_wit_2.
Axiom proof_of_mpz_abs_sub_safety_wit_3 : mpz_abs_sub_safety_wit_3.
Axiom proof_of_mpz_abs_sub_safety_wit_4 : mpz_abs_sub_safety_wit_4.
Axiom proof_of_mpz_abs_sub_safety_wit_5 : mpz_abs_sub_safety_wit_5.
Axiom proof_of_mpz_abs_sub_safety_wit_6 : mpz_abs_sub_safety_wit_6.
Axiom proof_of_mpz_abs_sub_safety_wit_7 : mpz_abs_sub_safety_wit_7.
Axiom proof_of_mpz_abs_sub_safety_wit_8 : mpz_abs_sub_safety_wit_8.
Axiom proof_of_mpz_abs_sub_safety_wit_9 : mpz_abs_sub_safety_wit_9.
Axiom proof_of_mpz_abs_sub_safety_wit_10 : mpz_abs_sub_safety_wit_10.
Axiom proof_of_mpz_abs_sub_safety_wit_11 : mpz_abs_sub_safety_wit_11.
Axiom proof_of_mpz_abs_sub_safety_wit_12 : mpz_abs_sub_safety_wit_12.
Axiom proof_of_mpz_abs_sub_entail_wit_1 : mpz_abs_sub_entail_wit_1.
Axiom proof_of_mpz_abs_sub_entail_wit_2 : mpz_abs_sub_entail_wit_2.
Axiom proof_of_mpz_abs_sub_entail_wit_3 : mpz_abs_sub_entail_wit_3.
Axiom proof_of_mpz_abs_sub_entail_wit_4 : mpz_abs_sub_entail_wit_4.
Axiom proof_of_mpz_abs_sub_return_wit_1 : mpz_abs_sub_return_wit_1.
Axiom proof_of_mpz_abs_sub_return_wit_2 : mpz_abs_sub_return_wit_2.
Axiom proof_of_mpz_abs_sub_return_wit_3 : mpz_abs_sub_return_wit_3.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_1 : mpz_abs_sub_partial_solve_wit_1.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_2_pure : mpz_abs_sub_partial_solve_wit_2_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_2 : mpz_abs_sub_partial_solve_wit_2.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_3 : mpz_abs_sub_partial_solve_wit_3.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_4_pure : mpz_abs_sub_partial_solve_wit_4_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_4 : mpz_abs_sub_partial_solve_wit_4.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_5_pure : mpz_abs_sub_partial_solve_wit_5_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_5 : mpz_abs_sub_partial_solve_wit_5.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_6_pure : mpz_abs_sub_partial_solve_wit_6_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_6 : mpz_abs_sub_partial_solve_wit_6.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_7_pure : mpz_abs_sub_partial_solve_wit_7_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_7 : mpz_abs_sub_partial_solve_wit_7.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_8_pure : mpz_abs_sub_partial_solve_wit_8_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_8 : mpz_abs_sub_partial_solve_wit_8.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_9_pure : mpz_abs_sub_partial_solve_wit_9_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_9 : mpz_abs_sub_partial_solve_wit_9.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_10_pure : mpz_abs_sub_partial_solve_wit_10_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_10 : mpz_abs_sub_partial_solve_wit_10.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_11_pure : mpz_abs_sub_partial_solve_wit_11_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_11 : mpz_abs_sub_partial_solve_wit_11.
Axiom proof_of_mpz_add_safety_wit_1 : mpz_add_safety_wit_1.
Axiom proof_of_mpz_add_safety_wit_2 : mpz_add_safety_wit_2.
Axiom proof_of_mpz_add_safety_wit_3 : mpz_add_safety_wit_3.
Axiom proof_of_mpz_add_safety_wit_4 : mpz_add_safety_wit_4.
Axiom proof_of_mpz_add_safety_wit_5 : mpz_add_safety_wit_5.
Axiom proof_of_mpz_add_return_wit_1 : mpz_add_return_wit_1.
Axiom proof_of_mpz_add_return_wit_2 : mpz_add_return_wit_2.
Axiom proof_of_mpz_add_return_wit_3 : mpz_add_return_wit_3.
Axiom proof_of_mpz_add_return_wit_4 : mpz_add_return_wit_4.
Axiom proof_of_mpz_add_partial_solve_wit_1 : mpz_add_partial_solve_wit_1.
Axiom proof_of_mpz_add_partial_solve_wit_2 : mpz_add_partial_solve_wit_2.
Axiom proof_of_mpz_add_partial_solve_wit_3 : mpz_add_partial_solve_wit_3.
Axiom proof_of_mpz_add_partial_solve_wit_4 : mpz_add_partial_solve_wit_4.
Axiom proof_of_mpz_add_partial_solve_wit_5 : mpz_add_partial_solve_wit_5.
Axiom proof_of_mpz_add_partial_solve_wit_6 : mpz_add_partial_solve_wit_6.
Axiom proof_of_mpz_add_partial_solve_wit_7 : mpz_add_partial_solve_wit_7.
Axiom proof_of_mpz_add_partial_solve_wit_8 : mpz_add_partial_solve_wit_8.
Axiom proof_of_mpz_add_partial_solve_wit_9 : mpz_add_partial_solve_wit_9.
Axiom proof_of_mpz_add_partial_solve_wit_10 : mpz_add_partial_solve_wit_10.
Axiom proof_of_mpz_sub_safety_wit_1 : mpz_sub_safety_wit_1.
Axiom proof_of_mpz_sub_safety_wit_2 : mpz_sub_safety_wit_2.
Axiom proof_of_mpz_sub_safety_wit_3 : mpz_sub_safety_wit_3.
Axiom proof_of_mpz_sub_safety_wit_4 : mpz_sub_safety_wit_4.
Axiom proof_of_mpz_sub_safety_wit_5 : mpz_sub_safety_wit_5.
Axiom proof_of_mpz_sub_return_wit_1 : mpz_sub_return_wit_1.
Axiom proof_of_mpz_sub_return_wit_2 : mpz_sub_return_wit_2.
Axiom proof_of_mpz_sub_return_wit_3 : mpz_sub_return_wit_3.
Axiom proof_of_mpz_sub_return_wit_4 : mpz_sub_return_wit_4.
Axiom proof_of_mpz_sub_partial_solve_wit_1 : mpz_sub_partial_solve_wit_1.
Axiom proof_of_mpz_sub_partial_solve_wit_2 : mpz_sub_partial_solve_wit_2.
Axiom proof_of_mpz_sub_partial_solve_wit_3 : mpz_sub_partial_solve_wit_3.
Axiom proof_of_mpz_sub_partial_solve_wit_4 : mpz_sub_partial_solve_wit_4.
Axiom proof_of_mpz_sub_partial_solve_wit_5 : mpz_sub_partial_solve_wit_5.
Axiom proof_of_mpz_sub_partial_solve_wit_6 : mpz_sub_partial_solve_wit_6.
Axiom proof_of_mpz_sub_partial_solve_wit_7 : mpz_sub_partial_solve_wit_7.
Axiom proof_of_mpz_sub_partial_solve_wit_8 : mpz_sub_partial_solve_wit_8.
Axiom proof_of_mpz_sub_partial_solve_wit_9 : mpz_sub_partial_solve_wit_9.
Axiom proof_of_mpz_sub_partial_solve_wit_10 : mpz_sub_partial_solve_wit_10.

End VC_Correct.
