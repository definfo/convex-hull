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
Require Import SimpleC.EE.LLM_bench.Engineering.string.string_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
Require Import string_strategy_goal.
Require Import string_strategy_proof.

(*----- Function memcpy -----*)

Definition memcpy_safety_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) ,
  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  (CharArray.undef_full dest_pre n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition memcpy_safety_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (CharArray.full dest_pre (i + 1 ) (app ((sublist (0) (i) (bytes))) ((cons ((Znth i bytes 0)) (nil)))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (CharArray.full src_pre n_pre bytes )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition memcpy_entail_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) ,
  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (CharArray.undef_full dest_pre n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ”
  &&  (CharArray.full dest_pre 0 (sublist (0) (0) (bytes)) )
  **  (CharArray.undef_seg dest_pre 0 n_pre )
  **  (CharArray.full src_pre n_pre bytes )
.

Definition memcpy_entail_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (CharArray.full dest_pre (i + 1 ) (app ((sublist (0) (i) (bytes))) ((cons ((Znth i bytes 0)) (nil)))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  (CharArray.full dest_pre (i + 1 ) (sublist (0) ((i + 1 )) (bytes)) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (CharArray.full src_pre n_pre bytes )
.

Definition memcpy_return_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (dest_pre = dest_pre) ”
  &&  (CharArray.full dest_pre n_pre bytes )
  **  (CharArray.full src_pre n_pre bytes )
.

Definition memcpy_partial_solve_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (i < n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((src_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i bytes 0))
  **  (CharArray.missing_i src_pre i 0 n_pre bytes )
  **  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
.

Definition memcpy_partial_solve_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (CharArray.full src_pre n_pre bytes )
  **  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((dest_pre + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i dest_pre i i n_pre )
  **  (CharArray.full src_pre n_pre bytes )
  **  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
.

(*----- Function memmove -----*)

Definition memmove_safety_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) ,
  “ (dest_pre < src_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  (CharArray.undef_full dest_pre n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition memmove_safety_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (CharArray.full dest_pre (i + 1 ) (app ((sublist (0) (i) (bytes))) ((cons ((Znth i bytes 0)) (nil)))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (CharArray.full src_pre n_pre bytes )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition memmove_safety_wit_3 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) ,
  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_seg dest_pre 0 i )
  **  (CharArray.full (dest_pre + (i * sizeof(CHAR) ) ) (n_pre - i ) (sublist (i) (n_pre) (bytes)) )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition memmove_safety_wit_4 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) ,
  “ (i > 0) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_seg dest_pre 0 i )
  **  (CharArray.full (dest_pre + (i * sizeof(CHAR) ) ) (n_pre - i ) (sublist (i) (n_pre) (bytes)) )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition memmove_entail_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) ,
  “ (dest_pre < src_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (CharArray.undef_full dest_pre n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ”
  &&  (CharArray.full dest_pre 0 (sublist (0) (0) (bytes)) )
  **  (CharArray.undef_seg dest_pre 0 n_pre )
  **  (CharArray.full src_pre n_pre bytes )
.

Definition memmove_entail_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (CharArray.full dest_pre (i + 1 ) (app ((sublist (0) (i) (bytes))) ((cons ((Znth i bytes 0)) (nil)))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  (CharArray.full dest_pre (i + 1 ) (sublist (0) ((i + 1 )) (bytes)) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (CharArray.full src_pre n_pre bytes )
.

Definition memmove_entail_wit_3 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) ,
  “ (dest_pre >= src_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (CharArray.undef_full dest_pre n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ”
  &&  (CharArray.undef_seg dest_pre 0 n_pre )
  **  (CharArray.full (dest_pre + (n_pre * sizeof(CHAR) ) ) (n_pre - n_pre ) (sublist (n_pre) (n_pre) (bytes)) )
  **  (CharArray.full src_pre n_pre bytes )
.

Definition memmove_entail_wit_4 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) ,
  “ (0 <= (n_pre - i )) ” 
  &&  “ (i > 0) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((dest_pre + ((i - 1 ) * sizeof(CHAR) ) )) # Char  |-> (Znth (i - 1 ) bytes 0))
  **  (CharArray.undef_missing_i dest_pre (i - 1 ) 0 i )
  **  (CharArray.full src_pre n_pre bytes )
  **  (CharArray.full (dest_pre + (i * sizeof(CHAR) ) ) (n_pre - i ) (sublist (i) (n_pre) (bytes)) )
|--
  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= n_pre) ”
  &&  (CharArray.undef_seg dest_pre 0 (i - 1 ) )
  **  (CharArray.full (dest_pre + ((i - 1 ) * sizeof(CHAR) ) ) (n_pre - (i - 1 ) ) (sublist ((i - 1 )) (n_pre) (bytes)) )
  **  (CharArray.full src_pre n_pre bytes )
.

Definition memmove_return_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (dest_pre = dest_pre) ”
  &&  (CharArray.full dest_pre n_pre bytes )
  **  (CharArray.full src_pre n_pre bytes )
.

Definition memmove_return_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) ,
  “ (i <= 0) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (CharArray.undef_seg dest_pre 0 i )
  **  (CharArray.full (dest_pre + (i * sizeof(CHAR) ) ) (n_pre - i ) (sublist (i) (n_pre) (bytes)) )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (dest_pre = dest_pre) ”
  &&  (CharArray.full dest_pre n_pre bytes )
  **  (CharArray.full src_pre n_pre bytes )
.

Definition memmove_partial_solve_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (i < n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((src_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i bytes 0))
  **  (CharArray.missing_i src_pre i 0 n_pre bytes )
  **  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
.

Definition memmove_partial_solve_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (CharArray.full src_pre n_pre bytes )
  **  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((dest_pre + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i dest_pre i i n_pre )
  **  (CharArray.full src_pre n_pre bytes )
  **  (CharArray.full dest_pre i (sublist (0) (i) (bytes)) )
.

Definition memmove_partial_solve_wit_3 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) ,
  “ (i > 0) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (CharArray.undef_seg dest_pre 0 i )
  **  (CharArray.full (dest_pre + (i * sizeof(CHAR) ) ) (n_pre - i ) (sublist (i) (n_pre) (bytes)) )
  **  (CharArray.full src_pre n_pre bytes )
|--
  “ (0 <= (n_pre - i )) ” 
  &&  “ (i > 0) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((src_pre + ((i - 1 ) * sizeof(CHAR) ) )) # Char  |-> (Znth (i - 1 ) bytes 0))
  **  (CharArray.missing_i src_pre (i - 1 ) 0 n_pre bytes )
  **  (CharArray.undef_seg dest_pre 0 i )
  **  (CharArray.full (dest_pre + (i * sizeof(CHAR) ) ) (n_pre - i ) (sublist (i) (n_pre) (bytes)) )
.

Definition memmove_partial_solve_wit_4 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (bytes: (@list Z)) (i: Z) ,
  “ (0 <= (n_pre - i )) ” 
  &&  “ (i > 0) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (CharArray.full src_pre n_pre bytes )
  **  (CharArray.undef_seg dest_pre 0 i )
  **  (CharArray.full (dest_pre + (i * sizeof(CHAR) ) ) (n_pre - i ) (sublist (i) (n_pre) (bytes)) )
|--
  “ (0 <= (n_pre - i )) ” 
  &&  “ (i > 0) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((dest_pre + ((i - 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i dest_pre (i - 1 ) 0 i )
  **  (CharArray.full src_pre n_pre bytes )
  **  (CharArray.full (dest_pre + (i * sizeof(CHAR) ) ) (n_pre - i ) (sublist (i) (n_pre) (bytes)) )
.

(*----- Function memset -----*)

Definition memset_safety_wit_1 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.undef_full s_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition memset_safety_wit_2 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (CharArray.full s_pre (i + 1 ) (app ((repeat_Z (c_pre) (i))) ((cons (c_pre) (nil)))) )
  **  (CharArray.undef_seg s_pre (i + 1 ) n_pre )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition memset_entail_wit_1 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ”
  &&  (CharArray.undef_full s_pre n_pre )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ”
  &&  (CharArray.full s_pre 0 (repeat_Z (c_pre) (0)) )
  **  (CharArray.undef_seg s_pre 0 n_pre )
.

Definition memset_entail_wit_2 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (CharArray.full s_pre (i + 1 ) (app ((repeat_Z (c_pre) (i))) ((cons (c_pre) (nil)))) )
  **  (CharArray.undef_seg s_pre (i + 1 ) n_pre )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  (CharArray.full s_pre (i + 1 ) (repeat_Z (c_pre) ((i + 1 ))) )
  **  (CharArray.undef_seg s_pre (i + 1 ) n_pre )
.

Definition memset_return_wit_1 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (CharArray.full s_pre i (repeat_Z (c_pre) (i)) )
  **  (CharArray.undef_seg s_pre i n_pre )
|--
  “ (s_pre = s_pre) ”
  &&  (CharArray.full s_pre n_pre (repeat_Z (c_pre) (n_pre)) )
.

Definition memset_partial_solve_wit_1 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (CharArray.full s_pre i (repeat_Z (c_pre) (i)) )
  **  (CharArray.undef_seg s_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i s_pre i i n_pre )
  **  (CharArray.full s_pre i (repeat_Z (c_pre) (i)) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_memcpy_safety_wit_1 : memcpy_safety_wit_1.
Axiom proof_of_memcpy_safety_wit_2 : memcpy_safety_wit_2.
Axiom proof_of_memcpy_entail_wit_1 : memcpy_entail_wit_1.
Axiom proof_of_memcpy_entail_wit_2 : memcpy_entail_wit_2.
Axiom proof_of_memcpy_return_wit_1 : memcpy_return_wit_1.
Axiom proof_of_memcpy_partial_solve_wit_1 : memcpy_partial_solve_wit_1.
Axiom proof_of_memcpy_partial_solve_wit_2 : memcpy_partial_solve_wit_2.
Axiom proof_of_memmove_safety_wit_1 : memmove_safety_wit_1.
Axiom proof_of_memmove_safety_wit_2 : memmove_safety_wit_2.
Axiom proof_of_memmove_safety_wit_3 : memmove_safety_wit_3.
Axiom proof_of_memmove_safety_wit_4 : memmove_safety_wit_4.
Axiom proof_of_memmove_entail_wit_1 : memmove_entail_wit_1.
Axiom proof_of_memmove_entail_wit_2 : memmove_entail_wit_2.
Axiom proof_of_memmove_entail_wit_3 : memmove_entail_wit_3.
Axiom proof_of_memmove_entail_wit_4 : memmove_entail_wit_4.
Axiom proof_of_memmove_return_wit_1 : memmove_return_wit_1.
Axiom proof_of_memmove_return_wit_2 : memmove_return_wit_2.
Axiom proof_of_memmove_partial_solve_wit_1 : memmove_partial_solve_wit_1.
Axiom proof_of_memmove_partial_solve_wit_2 : memmove_partial_solve_wit_2.
Axiom proof_of_memmove_partial_solve_wit_3 : memmove_partial_solve_wit_3.
Axiom proof_of_memmove_partial_solve_wit_4 : memmove_partial_solve_wit_4.
Axiom proof_of_memset_safety_wit_1 : memset_safety_wit_1.
Axiom proof_of_memset_safety_wit_2 : memset_safety_wit_2.
Axiom proof_of_memset_entail_wit_1 : memset_entail_wit_1.
Axiom proof_of_memset_entail_wit_2 : memset_entail_wit_2.
Axiom proof_of_memset_return_wit_1 : memset_return_wit_1.
Axiom proof_of_memset_partial_solve_wit_1 : memset_partial_solve_wit_1.

End VC_Correct.
