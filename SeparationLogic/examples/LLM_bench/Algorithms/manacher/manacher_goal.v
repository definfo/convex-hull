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
Require Import SimpleC.EE.LLM_bench.Algorithms.manacher.manacher_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.EE.LLM_bench.Engineering.string Require Import string_strategy_goal.
From SimpleC.EE.LLM_bench.Engineering.string Require Import string_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function longestPalindrom -----*)

Definition longestPalindrom_safety_wit_1 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_2 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ”
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_3 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ”
  &&  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_4 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ”
  &&  ((( &( "id" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_5 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ”
  &&  ((( &( "limit" ) )) # Int  |->_)
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_6 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ”
  &&  ((( &( "maxLen" ) )) # Int  |->_)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_7 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ”
  &&  ((( &( "maxId" ) )) # Int  |->_)
  **  ((( &( "maxLen" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_8 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ”
  &&  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "maxId" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_9 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ”
  &&  ((( &( "mirror" ) )) # Int  |->_)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "maxId" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_10 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ”
  &&  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "mirror" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "maxId" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_11 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ”
  &&  (IntArray.undef_full ( &( "p" ) ) 2003 )
  **  (CharArray.undef_full ( &( "s2" ) ) 2003 )
  **  ((( &( "ret" ) )) # Int  |-> 0)
  **  ((( &( "mirror" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "maxId" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_12 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ”
  &&  (IntArray.undef_full ( &( "p" ) ) 2003 )
  **  (CharArray.undef_full ( &( "s2" ) ) 2003 )
  **  ((( &( "ret" ) )) # Int  |-> 0)
  **  ((( &( "mirror" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "maxId" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_13 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ”
  &&  (((( &( "p" ) ) + (0 * sizeof(INT) ) )) # Int  |-> 0)
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full ( &( "s2" ) ) 2003 )
  **  ((( &( "ret" ) )) # Int  |-> 0)
  **  ((( &( "mirror" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "maxId" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_14 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ”
  &&  (((( &( "p" ) ) + (0 * sizeof(INT) ) )) # Int  |-> 0)
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full ( &( "s2" ) ) 2003 )
  **  ((( &( "ret" ) )) # Int  |-> 0)
  **  ((( &( "mirror" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "maxId" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (36 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 36) ”
.

Definition longestPalindrom_safety_wit_15 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (((2 * i ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * i ) + 1 )) ”
.

Definition longestPalindrom_safety_wit_16 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ ((2 * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i )) ”
.

Definition longestPalindrom_safety_wit_17 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition longestPalindrom_safety_wit_18 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longestPalindrom_safety_wit_19 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (35 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 35) ”
.

Definition longestPalindrom_safety_wit_20 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) (nil)))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (((2 * i ) + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * i ) + 2 )) ”
.

Definition longestPalindrom_safety_wit_21 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) (nil)))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ ((2 * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i )) ”
.

Definition longestPalindrom_safety_wit_22 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) (nil)))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition longestPalindrom_safety_wit_23 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) (nil)))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition longestPalindrom_safety_wit_24 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 ((((2 * i ) + 1 ) + 1 ) + 1 ) (app ((app (s2_pre) ((cons (35) (nil))))) ((cons ((Znth i (c_string (str)) 0)) (nil)))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 2 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition longestPalindrom_safety_wit_25 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (((2 * i ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * i ) + 1 )) ”
.

Definition longestPalindrom_safety_wit_26 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ ((2 * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i )) ”
.

Definition longestPalindrom_safety_wit_27 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition longestPalindrom_safety_wit_28 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longestPalindrom_safety_wit_29 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (35 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 35) ”
.

Definition longestPalindrom_safety_wit_30 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) (nil)))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (((2 * i ) + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * i ) + 2 )) ”
.

Definition longestPalindrom_safety_wit_31 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) (nil)))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ ((2 * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i )) ”
.

Definition longestPalindrom_safety_wit_32 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) (nil)))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition longestPalindrom_safety_wit_33 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) (nil)))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition longestPalindrom_safety_wit_34 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) (nil)))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> ((2 * i ) + 2 ))
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_35 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 ((((2 * i ) + 1 ) + 1 ) + 1 ) (app ((app (s2_pre) ((cons (35) (nil))))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 2 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> ((2 * i ) + 2 ))
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_36 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 ((((2 * i ) + 1 ) + 1 ) + 1 ) (app ((app (s2_pre) ((cons (35) (nil))))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 2 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> ((2 * i ) + 2 ))
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_37 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 ((((2 * i ) + 1 ) + 1 ) + 1 ) (app ((app (s2_pre) ((cons (35) (nil))))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 2 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> ((2 * i ) + 2 ))
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_38 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 ((((2 * i ) + 1 ) + 1 ) + 1 ) (app ((app (s2_pre) ((cons (35) (nil))))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 2 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> ((2 * i ) + 2 ))
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> 0)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_39 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 ((((2 * i ) + 1 ) + 1 ) + 1 ) (app ((app (s2_pre) ((cons (35) (nil))))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 2 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> ((2 * i ) + 2 ))
  **  ((( &( "id" ) )) # Int  |-> 0)
  **  ((( &( "limit" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> 0)
  **  ((( &( "maxId" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longestPalindrom_safety_wit_40 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_cur: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) ,
  “ (i < limit) ” 
  &&  “ (i < len) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ (((2 * id ) - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * id ) - i )) ”
.

Definition longestPalindrom_safety_wit_41 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_cur: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) ,
  “ (i < limit) ” 
  &&  “ (i < len) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ ((2 * id ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * id )) ”
.

Definition longestPalindrom_safety_wit_42 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_cur: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) ,
  “ (i < limit) ” 
  &&  “ (i < len) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition longestPalindrom_safety_wit_43 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < i) ” 
  &&  “ (mirror = ((2 * id ) - i )) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (i < limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ ((limit - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (limit - i )) ”
.

Definition longestPalindrom_safety_wit_44 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) ,
  “ ((Znth (mirror - 0 ) p_cur 0) >= (limit - i )) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < i) ” 
  &&  “ (mirror = ((2 * id ) - i )) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (i < limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ ((limit - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (limit - i )) ”
.

Definition longestPalindrom_safety_wit_45 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_cur: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) ,
  “ (i >= limit) ” 
  &&  “ (i < len) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longestPalindrom_safety_wit_46 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ ((i - r ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - r )) ”
.

Definition longestPalindrom_safety_wit_47 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ ((i + r ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + r )) ”
.

Definition longestPalindrom_safety_wit_48 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full: (@list Z)) (p_written: (@list Z)) (len: Z) (i: Z) (j: Z) (ret: Z) (r: Z) (id: Z) (limit: Z) (mirror: Z) (maxLen: Z) (maxId: Z) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 < (i - r )) ” 
  &&  “ ((i + r ) < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionAfterMatch s2_full len i r ) ”
  &&  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ ((r + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition longestPalindrom_safety_wit_49 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0)) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ ((i + r ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + r )) ”
.

Definition longestPalindrom_safety_wit_50 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ ((i + r ) > limit) ” 
  &&  “ ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0)) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ ((i + r ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + r )) ”
.

Definition longestPalindrom_safety_wit_51 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ ((i + r ) <= limit) ” 
  &&  “ ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0)) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ ((r - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r - 1 )) ”
.

Definition longestPalindrom_safety_wit_52 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ ((i + r ) <= limit) ” 
  &&  “ ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0)) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longestPalindrom_safety_wit_53 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ ((i + r ) > limit) ” 
  &&  “ ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0)) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "id" ) )) # Int  |-> i)
  **  ((( &( "limit" ) )) # Int  |-> (i + r ))
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ ((r - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r - 1 )) ”
.

Definition longestPalindrom_safety_wit_54 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ ((i + r ) > limit) ” 
  &&  “ ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0)) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "id" ) )) # Int  |-> i)
  **  ((( &( "limit" ) )) # Int  |-> (i + r ))
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longestPalindrom_safety_wit_55 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ (maxLen >= (r - 1 )) ” 
  &&  “ ((i + r ) <= limit) ” 
  &&  “ ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0)) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_56 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ (maxLen >= (r - 1 )) ” 
  &&  “ ((i + r ) > limit) ” 
  &&  “ ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0)) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "id" ) )) # Int  |-> i)
  **  ((( &( "limit" ) )) # Int  |-> (i + r ))
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_57 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ (maxLen < (r - 1 )) ” 
  &&  “ ((i + r ) <= limit) ” 
  &&  “ ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0)) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "maxId" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_58 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ (maxLen < (r - 1 )) ” 
  &&  “ ((i + r ) > limit) ” 
  &&  “ ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0)) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "id" ) )) # Int  |-> i)
  **  ((( &( "limit" ) )) # Int  |-> (i + r ))
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "maxId" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_59 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ (maxLen < (r - 1 )) ” 
  &&  “ ((i + r ) > limit) ” 
  &&  “ ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0)) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> i)
  **  ((( &( "limit" ) )) # Int  |-> (i + r ))
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "maxId" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_60 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ (maxLen < (r - 1 )) ” 
  &&  “ ((i + r ) <= limit) ” 
  &&  “ ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0)) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "maxId" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_61 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ (maxLen >= (r - 1 )) ” 
  &&  “ ((i + r ) > limit) ” 
  &&  “ ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0)) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> i)
  **  ((( &( "limit" ) )) # Int  |-> (i + r ))
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_62 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ (maxLen >= (r - 1 )) ” 
  &&  “ ((i + r ) <= limit) ” 
  &&  “ ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0)) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_63 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ (maxLen >= (r - 1 )) ” 
  &&  “ ((i + r ) <= limit) ” 
  &&  “ ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0)) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition longestPalindrom_safety_wit_64 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ (maxLen >= (r - 1 )) ” 
  &&  “ ((i + r ) > limit) ” 
  &&  “ ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0)) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> i)
  **  ((( &( "limit" ) )) # Int  |-> (i + r ))
  **  ((( &( "mirror" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition longestPalindrom_safety_wit_65 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ (maxLen < (r - 1 )) ” 
  &&  “ ((i + r ) <= limit) ” 
  &&  “ ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0)) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "mirror" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "maxId" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition longestPalindrom_safety_wit_66 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ (maxLen < (r - 1 )) ” 
  &&  “ ((i + r ) > limit) ” 
  &&  “ ((Znth ((i + r ) - 0 ) s2_full 0) <> (Znth ((i - r ) - 0 ) s2_full 0)) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "id" ) )) # Int  |-> i)
  **  ((( &( "limit" ) )) # Int  |-> (i + r ))
  **  ((( &( "mirror" ) )) # Int  |-> 0)
  **  ((( &( "maxLen" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "maxId" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition longestPalindrom_safety_wit_67 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_cur: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) ,
  “ (i >= len) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_safety_wit_68 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_cur: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) ,
  “ (i >= len) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ ((maxId - maxLen ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (maxId - maxLen )) ”
.

Definition longestPalindrom_safety_wit_69 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done: (@list Z)) (s2_full: (@list Z)) (out_prefix: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= i) ” 
  &&  “ (i <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  (store_string s_pre str )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  “ ((maxId + maxLen ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (maxId + maxLen )) ”
.

Definition longestPalindrom_safety_wit_70 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done: (@list Z)) (s2_full: (@list Z)) (out_prefix: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i <= (maxId + maxLen )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= i) ” 
  &&  “ (i <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  “ (35 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 35) ”
.

Definition longestPalindrom_safety_wit_71 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done: (@list Z)) (s2_full: (@list Z)) (out_prefix: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) ,
  “ ((Znth (i - 0 ) s2_full 0) <> 35) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i <= (maxId + maxLen )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= i) ” 
  &&  “ (i <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (CharArray.full output_pre (j + 1 ) (app (out_prefix) ((cons ((Znth (i - 0 ) s2_full 0)) (nil)))) )
  **  (CharArray.undef_seg output_pre (j + 1 ) (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition longestPalindrom_safety_wit_72 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done: (@list Z)) (s2_full: (@list Z)) (out_prefix: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) ,
  “ ((Znth (i - 0 ) s2_full 0) = 35) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i <= (maxId + maxLen )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= i) ” 
  &&  “ (i <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition longestPalindrom_safety_wit_73 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done: (@list Z)) (s2_full: (@list Z)) (out_prefix: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) ,
  “ ((Znth (i - 0 ) s2_full 0) <> 35) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i <= (maxId + maxLen )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= i) ” 
  &&  “ (i <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (CharArray.full output_pre (j + 1 ) (app (out_prefix) ((cons ((Znth (i - 0 ) s2_full 0)) (nil)))) )
  **  (CharArray.undef_seg output_pre (j + 1 ) (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition longestPalindrom_safety_wit_74 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done: (@list Z)) (s2_full: (@list Z)) (out_prefix: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) ,
  “ (i > (maxId + maxLen )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= i) ” 
  &&  “ (i <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "maxLen" ) )) # Int  |-> maxLen)
  **  ((( &( "maxId" ) )) # Int  |-> maxId)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "mirror" ) )) # Int  |-> mirror)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "limit" ) )) # Int  |-> limit)
  **  ((( &( "id" ) )) # Int  |-> id)
  **  (store_string s_pre str )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longestPalindrom_entail_wit_1 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ”
  &&  (CharArray.undef_seg ( &( "s2" ) ) (0 + 1 ) 2003 )
  **  (((( &( "s2" ) ) + (0 * sizeof(CHAR) ) )) # Char  |-> 36)
  **  (((( &( "p" ) ) + (0 * sizeof(INT) ) )) # Int  |-> 0)
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  EX (p_pre: (@list Z))  (s2_pre: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * 0 ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre 0 ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * 0 ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * 0 ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
.

Definition longestPalindrom_entail_wit_2 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre_2: (@list Z)) (s2_pre_2: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre_2)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre_2)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre_2 i ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 ((((2 * i ) + 1 ) + 1 ) + 1 ) (app ((app (s2_pre_2) ((cons (35) (nil))))) ((cons ((Znth i (c_string (str)) 0)) (nil)))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 2 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre_2 )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  EX (p_pre: (@list Z))  (s2_pre: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * (i + 1 ) ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre (i + 1 ) ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * (i + 1 ) ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * (i + 1 ) ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
.

Definition longestPalindrom_entail_wit_3 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre_2: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre_2)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 ((((2 * i ) + 1 ) + 1 ) + 1 ) (app ((app (s2_pre) ((cons (35) (nil))))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 2 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre_2 )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  EX (p_pre: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (((2 * i ) + 2 ) = ((2 * n_pre ) + 2 )) ” 
  &&  “ (((2 * i ) + 2 ) <= 2002) ” 
  &&  “ (1 = 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_full)) = (((2 * i ) + 2 ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedString str s2_full ((2 * i ) + 2 ) ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 2 ) + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 2 ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
.

Definition longestPalindrom_entail_wit_4 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_pre: (@list Z)) (len: Z) (i: Z) (id: Z) (limit: Z) (maxLen: Z) (maxId: Z) (j: Z) (r: Z) (mirror: Z) (ret: Z) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (i = 1) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_full_2)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedString str s2_full_2 len ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  EX (p_cur: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
.

Definition longestPalindrom_entail_wit_5 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_cur_2: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) ,
  “ (i < limit) ” 
  &&  “ (i < len) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ ((Zlength (s2_full_2)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur_2)) = i) ” 
  &&  “ (ManacherLoopState str s2_full_2 len p_cur_2 i id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur_2 )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  EX (p_cur: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= ((2 * id ) - i )) ” 
  &&  “ (((2 * id ) - i ) < i) ” 
  &&  “ (((2 * id ) - i ) = ((2 * id ) - i )) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (i < limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
.

Definition longestPalindrom_entail_wit_6_1 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) ,
  “ ((Znth (mirror - 0 ) p_cur 0) < (limit - i )) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < i) ” 
  &&  “ (mirror = ((2 * id ) - i )) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (i < limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ ((Zlength (s2_full_2)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen ) ”
  &&  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) (app (p_cur) ((cons ((Znth (mirror - 0 ) p_cur 0)) (nil)))) )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
|--
  EX (p_written: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= (Znth (mirror - 0 ) p_cur 0)) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - (Znth (mirror - 0 ) p_cur 0) )) ” 
  &&  “ ((i + (Znth (mirror - 0 ) p_cur 0) ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i (Znth (mirror - 0 ) p_cur 0) id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i (Znth (mirror - 0 ) p_cur 0) ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
.

Definition longestPalindrom_entail_wit_6_2 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) ,
  “ ((Znth (mirror - 0 ) p_cur 0) >= (limit - i )) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < i) ” 
  &&  “ (mirror = ((2 * id ) - i )) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (i < limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ ((Zlength (s2_full_2)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen ) ”
  &&  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) (app (p_cur) ((cons ((limit - i )) (nil)))) )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
|--
  EX (p_written: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= (limit - i )) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - (limit - i ) )) ” 
  &&  “ ((i + (limit - i ) ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i (limit - i ) id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i (limit - i ) ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
.

Definition longestPalindrom_entail_wit_6_3 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_cur: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i >= limit) ” 
  &&  “ (i < len) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ ((Zlength (s2_full_2)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen ) ”
  &&  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) (app (p_cur) ((cons (1) (nil)))) )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
|--
  EX (p_written: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i 1 id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i 1 ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
.

Definition longestPalindrom_entail_wit_7 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_written_2: (@list Z)) (len: Z) (i: Z) (j: Z) (ret: Z) (r: Z) (id: Z) (limit: Z) (mirror: Z) (maxLen: Z) (maxId: Z) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full_2)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written_2)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full_2 len p_written_2 i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full_2 len i r ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written_2 )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  EX (p_written: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
.

Definition longestPalindrom_entail_wit_8 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written_2: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ ((Znth ((i + r ) - 0 ) s2_full_2 0) = (Znth ((i - r ) - 0 ) s2_full_2 0)) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full_2)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written_2)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full_2 len p_written_2 i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full_2 len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written_2 )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  EX (p_written: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 < (i - r )) ” 
  &&  “ ((i + r ) < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionAfterMatch s2_full len i r ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
.

Definition longestPalindrom_entail_wit_9 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_written_2: (@list Z)) (len: Z) (i: Z) (j: Z) (ret: Z) (r: Z) (id: Z) (limit: Z) (mirror: Z) (maxLen: Z) (maxId: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 < (i - r )) ” 
  &&  “ ((i + r ) < len) ” 
  &&  “ ((Zlength (s2_full_2)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written_2)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full_2 len p_written_2 i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionAfterMatch s2_full_2 len i r ) ”
  &&  (IntArray.full ( &( "p" ) ) (i + 1 ) (replace_Znth (i) ((r + 1 )) (p_written_2)) )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  EX (p_written: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= (r + 1 )) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - (r + 1 ) )) ” 
  &&  “ ((i + (r + 1 ) ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i (r + 1 ) id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i (r + 1 ) ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
.

Definition longestPalindrom_entail_wit_10_1 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ (maxLen >= (r - 1 )) ” 
  &&  “ ((i + r ) <= limit) ” 
  &&  “ ((Znth ((i + r ) - 0 ) s2_full_2 0) <> (Znth ((i - r ) - 0 ) s2_full_2 0)) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full_2)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full_2 len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full_2 len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  EX (p_next: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_next)) = (i + 1 )) ” 
  &&  “ (ManacherLoopState str s2_full len p_next (i + 1 ) id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_next )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
.

Definition longestPalindrom_entail_wit_10_2 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ (maxLen >= (r - 1 )) ” 
  &&  “ ((i + r ) > limit) ” 
  &&  “ ((Znth ((i + r ) - 0 ) s2_full_2 0) <> (Znth ((i - r ) - 0 ) s2_full_2 0)) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full_2)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full_2 len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full_2 len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  EX (p_next: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_next)) = (i + 1 )) ” 
  &&  “ (ManacherLoopState str s2_full len p_next (i + 1 ) i (i + r ) maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_next )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
.

Definition longestPalindrom_entail_wit_10_3 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ (maxLen < (r - 1 )) ” 
  &&  “ ((i + r ) <= limit) ” 
  &&  “ ((Znth ((i + r ) - 0 ) s2_full_2 0) <> (Znth ((i - r ) - 0 ) s2_full_2 0)) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full_2)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full_2 len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full_2 len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  EX (p_next: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= (r - 1 )) ” 
  &&  “ ((r - 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_next)) = (i + 1 )) ” 
  &&  “ (ManacherLoopState str s2_full len p_next (i + 1 ) id limit i (r - 1 ) ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_next )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
.

Definition longestPalindrom_entail_wit_10_4 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ (maxLen < (r - 1 )) ” 
  &&  “ ((i + r ) > limit) ” 
  &&  “ ((Znth ((i + r ) - 0 ) s2_full_2 0) <> (Znth ((i - r ) - 0 ) s2_full_2 0)) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full_2)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full_2 len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full_2 len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  EX (p_next: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= (r - 1 )) ” 
  &&  “ ((r - 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_next)) = (i + 1 )) ” 
  &&  “ (ManacherLoopState str s2_full len p_next (i + 1 ) i (i + r ) i (r - 1 ) ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_next )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
.

Definition longestPalindrom_entail_wit_11 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_next: (@list Z)) (len: Z) (i: Z) (j: Z) (r: Z) (mirror: Z) (ret: Z) (maxLen: Z) (maxId: Z) (limit: Z) (id: Z) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ ((Zlength (s2_full_2)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_next)) = i) ” 
  &&  “ (ManacherLoopState str s2_full_2 len p_next i id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_next )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  EX (p_cur: (@list Z))  (s2_full: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
.

Definition longestPalindrom_entail_wit_12 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_cur: (@list Z)) (s2_full_2: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) ,
  “ (i >= len) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ ((Zlength (s2_full_2)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full_2 len p_cur i id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  EX (p_done: (@list Z))  (s2_full: (@list Z))  (out_pre: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) = (maxId - maxLen )) ” 
  &&  “ (0 = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (out_pre = nil) ” 
  &&  “ (OutputCopyPrefix s2_full out_pre (maxId - maxLen ) (maxId - maxLen ) 0 ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
.

Definition longestPalindrom_entail_wit_13 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full_2: (@list Z)) (p_done_2: (@list Z)) (out_pre: (@list Z)) (len: Z) (maxLen: Z) (maxId: Z) (i: Z) (j: Z) (r: Z) (mirror: Z) (ret: Z) (limit: Z) (id: Z) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ (i = (maxId - maxLen )) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (out_pre = nil) ” 
  &&  “ (OutputCopyPrefix s2_full_2 out_pre (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur_2: Z) , ((((maxId - maxLen ) <= cur_2) /\ (cur_2 <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full_2 (maxId - maxLen ) cur_2 maxLen )) ” 
  &&  “ ((Zlength (s2_full_2)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done_2)) = len) ” 
  &&  “ (ManacherLoopState str s2_full_2 len p_done_2 len id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done_2 )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  EX (p_done: (@list Z))  (s2_full: (@list Z))  (out_prefix: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= i) ” 
  &&  “ (i <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
.

Definition longestPalindrom_entail_wit_14_1 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done_2: (@list Z)) (s2_full_2: (@list Z)) (out_prefix_2: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) ,
  “ ((Znth (i - 0 ) s2_full_2 0) <> 35) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i <= (maxId + maxLen )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= i) ” 
  &&  “ (i <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full_2 out_prefix_2 (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full_2 (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full_2)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done_2)) = len) ” 
  &&  “ (ManacherLoopState str s2_full_2 len p_done_2 len id limit maxId maxLen ) ”
  &&  (CharArray.full output_pre (j + 1 ) (app (out_prefix_2) ((cons ((Znth (i - 0 ) s2_full_2 0)) (nil)))) )
  **  (CharArray.undef_seg output_pre (j + 1 ) (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done_2 )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  EX (p_done: (@list Z))  (s2_full: (@list Z))  (out_prefix: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) (i + 1 ) (j + 1 ) ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.full output_pre (j + 1 ) out_prefix )
  **  (CharArray.undef_seg output_pre (j + 1 ) (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
.

Definition longestPalindrom_entail_wit_14_2 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done_2: (@list Z)) (s2_full_2: (@list Z)) (out_prefix_2: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) ,
  “ ((Znth (i - 0 ) s2_full_2 0) = 35) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i <= (maxId + maxLen )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= i) ” 
  &&  “ (i <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full_2 out_prefix_2 (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full_2 (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full_2)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done_2)) = len) ” 
  &&  “ (ManacherLoopState str s2_full_2 len p_done_2 len id limit maxId maxLen ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.full output_pre j out_prefix_2 )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done_2 )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  EX (p_done: (@list Z))  (s2_full: (@list Z))  (out_prefix: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) (i + 1 ) j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
.

Definition longestPalindrom_entail_wit_15 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done_2: (@list Z)) (s2_full_2: (@list Z)) (out_prefix: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i > (maxId + maxLen )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= i) ” 
  &&  “ (i <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full_2 out_prefix (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full_2 (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full_2)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done_2)) = len) ” 
  &&  “ (ManacherLoopState str s2_full_2 len p_done_2 len id limit maxId maxLen ) ”
  &&  (CharArray.full output_pre (j + 1 ) (app (out_prefix) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg output_pre (j + 1 ) (n_pre + 1 ) )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full_2 )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done_2 )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  EX (p_done: (@list Z))  (s2_full: (@list Z))  (out: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (maxLen = maxLen) ” 
  &&  “ (i = ((maxId + maxLen ) + 1 )) ” 
  &&  “ (j = maxLen) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (OutputCopyDone str s2_full out len maxId maxLen maxLen ) ” 
  &&  “ (LongestPalindromeResult str out maxLen ) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ”
  &&  (store_string s_pre str )
  **  (CharArray.full output_pre (maxLen + 1 ) (app (out) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg output_pre (maxLen + 1 ) (n_pre + 1 ) )
  **  (CharArray.undef_full ( &( "s2" ) ) 2003 )
  **  (IntArray.undef_full ( &( "p" ) ) 2003 )
.

Definition longestPalindrom_return_wit_1 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full: (@list Z)) (p_done: (@list Z)) (out_2: (@list Z)) (len: Z) (ret: Z) (maxLen: Z) (i: Z) (maxId: Z) (j: Z) (id: Z) (limit: Z) (r: Z) (mirror: Z) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (ret = maxLen) ” 
  &&  “ (i = ((maxId + maxLen ) + 1 )) ” 
  &&  “ (j = ret) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (1 <= ret) ” 
  &&  “ (ret <= n_pre) ” 
  &&  “ (OutputCopyDone str s2_full out_2 len maxId maxLen ret ) ” 
  &&  “ (LongestPalindromeResult str out_2 ret ) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ”
  &&  (store_string s_pre str )
  **  (CharArray.full output_pre (ret + 1 ) (app (out_2) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg output_pre (ret + 1 ) (n_pre + 1 ) )
|--
  EX (out: (@list Z)) ,
  “ (LongestPalindromeResult str out ret ) ” 
  &&  “ (1 <= ret) ” 
  &&  “ (ret <= n_pre) ”
  &&  (store_string s_pre str )
  **  (CharArray.full output_pre (ret + 1 ) (app (out) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg output_pre (ret + 1 ) (n_pre + 1 ) )
.

Definition longestPalindrom_partial_solve_wit_1 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ”
  &&  (IntArray.undef_full ( &( "p" ) ) 2003 )
  **  (CharArray.undef_full ( &( "s2" ) ) 2003 )
  **  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ”
  &&  (((( &( "p" ) ) + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full ( &( "s2" ) ) 2003 )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
.

Definition longestPalindrom_partial_solve_wit_2 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ”
  &&  (((( &( "p" ) ) + (0 * sizeof(INT) ) )) # Int  |-> 0)
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full ( &( "s2" ) ) 2003 )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ”
  &&  (((( &( "s2" ) ) + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i ( &( "s2" ) ) 0 0 2003 )
  **  (((( &( "p" ) ) + (0 * sizeof(INT) ) )) # Int  |-> 0)
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
.

Definition longestPalindrom_partial_solve_wit_3 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (((( &( "s2" ) ) + (((2 * i ) + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_missing_i ( &( "s2" ) ) ((2 * i ) + 1 ) ((2 * i ) + 1 ) 2003 )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
.

Definition longestPalindrom_partial_solve_wit_4 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) (nil)))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (c_string (str)) 0))
  **  (CharArray.missing_i s_pre i 0 ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) (nil)))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
.

Definition longestPalindrom_partial_solve_wit_5 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) (nil)))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (((( &( "s2" ) ) + (((2 * i ) + 2 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i ( &( "s2" ) ) ((2 * i ) + 2 ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) (nil)))) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
.

Definition longestPalindrom_partial_solve_wit_6 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (CharArray.undef_seg ( &( "s2" ) ) ((2 * i ) + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (((( &( "s2" ) ) + (((2 * i ) + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_missing_i ( &( "s2" ) ) ((2 * i ) + 1 ) ((2 * i ) + 1 ) 2003 )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 ((2 * i ) + 1 ) s2_pre )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
.

Definition longestPalindrom_partial_solve_wit_7 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_pre: (@list Z)) (s2_pre: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (len: Z) (j: Z) (i: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) (nil)))) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (id = 0) ” 
  &&  “ (limit = 0) ” 
  &&  “ (maxLen = 0) ” 
  &&  “ (maxId = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ ((Zlength (s2_pre)) = ((2 * i ) + 1 )) ” 
  &&  “ ((Zlength (p_pre)) = 1) ” 
  &&  “ (ManacherTransformedPrefix str s2_pre i ) ”
  &&  (((( &( "s2" ) ) + (((2 * i ) + 2 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i ( &( "s2" ) ) ((2 * i ) + 2 ) (((2 * i ) + 1 ) + 1 ) 2003 )
  **  (CharArray.seg ( &( "s2" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app (s2_pre) ((cons (35) (nil)))) )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (IntArray.seg ( &( "p" ) ) 0 1 p_pre )
  **  (IntArray.undef_seg ( &( "p" ) ) 1 2003 )
.

Definition longestPalindrom_partial_solve_wit_8 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < i) ” 
  &&  “ (mirror = ((2 * id ) - i )) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (i < limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < i) ” 
  &&  “ (mirror = ((2 * id ) - i )) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (i < limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  (((( &( "p" ) ) + (mirror * sizeof(INT) ) )) # Int  |-> (Znth (mirror - 0 ) p_cur 0))
  **  (IntArray.missing_i ( &( "p" ) ) mirror 0 i p_cur )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
.

Definition longestPalindrom_partial_solve_wit_9 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) ,
  “ ((Znth (mirror - 0 ) p_cur 0) < (limit - i )) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < i) ” 
  &&  “ (mirror = ((2 * id ) - i )) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (i < limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ ((Znth (mirror - 0 ) p_cur 0) < (limit - i )) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < i) ” 
  &&  “ (mirror = ((2 * id ) - i )) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (i < limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  (((( &( "p" ) ) + (mirror * sizeof(INT) ) )) # Int  |-> (Znth (mirror - 0 ) p_cur 0))
  **  (IntArray.missing_i ( &( "p" ) ) mirror 0 i p_cur )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
.

Definition longestPalindrom_partial_solve_wit_10 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) ,
  “ ((Znth (mirror - 0 ) p_cur 0) < (limit - i )) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < i) ” 
  &&  “ (mirror = ((2 * id ) - i )) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (i < limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ ((Znth (mirror - 0 ) p_cur 0) < (limit - i )) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < i) ” 
  &&  “ (mirror = ((2 * id ) - i )) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (i < limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  (((( &( "p" ) ) + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
.

Definition longestPalindrom_partial_solve_wit_11 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full: (@list Z)) (p_cur: (@list Z)) (len: Z) (i: Z) (mirror: Z) (id: Z) (j: Z) (r: Z) (ret: Z) (limit: Z) (maxLen: Z) (maxId: Z) ,
  “ ((Znth (mirror - 0 ) p_cur 0) >= (limit - i )) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < i) ” 
  &&  “ (mirror = ((2 * id ) - i )) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (i < limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ ((Znth (mirror - 0 ) p_cur 0) >= (limit - i )) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < i) ” 
  &&  “ (mirror = ((2 * id ) - i )) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (i < limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  (((( &( "p" ) ) + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
.

Definition longestPalindrom_partial_solve_wit_12 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_cur: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (limit: Z) (id: Z) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (len: Z) ,
  “ (i >= limit) ” 
  &&  “ (i < len) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
  **  (IntArray.undef_seg ( &( "p" ) ) i 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i >= limit) ” 
  &&  “ (i < len) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (j = 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_cur)) = i) ” 
  &&  “ (ManacherLoopState str s2_full len p_cur i id limit maxId maxLen ) ”
  &&  (((( &( "p" ) ) + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 i p_cur )
.

Definition longestPalindrom_partial_solve_wit_13 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (((( &( "s2" ) ) + ((i + r ) * sizeof(CHAR) ) )) # Char  |-> (Znth ((i + r ) - 0 ) s2_full 0))
  **  (CharArray.missing_i ( &( "s2" ) ) (i + r ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
.

Definition longestPalindrom_partial_solve_wit_14 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (p_written: (@list Z)) (s2_full: (@list Z)) (maxId: Z) (maxLen: Z) (mirror: Z) (limit: Z) (id: Z) (r: Z) (ret: Z) (j: Z) (i: Z) (len: Z) ,
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 <= (i - r )) ” 
  &&  “ ((i + r ) <= len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionCandidate s2_full len i r ) ”
  &&  (((( &( "s2" ) ) + ((i - r ) * sizeof(CHAR) ) )) # Char  |-> (Znth ((i - r ) - 0 ) s2_full 0))
  **  (CharArray.missing_i ( &( "s2" ) ) (i - r ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
.

Definition longestPalindrom_partial_solve_wit_15 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (s2_full: (@list Z)) (p_written: (@list Z)) (len: Z) (i: Z) (j: Z) (ret: Z) (r: Z) (id: Z) (limit: Z) (mirror: Z) (maxLen: Z) (maxId: Z) ,
  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 < (i - r )) ” 
  &&  “ ((i + r ) < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionAfterMatch s2_full len i r ) ”
  &&  (store_string s_pre str )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 (i + 1 ) p_written )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (j = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (1 <= r) ” 
  &&  “ (0 <= id) ” 
  &&  “ (id < len) ” 
  &&  “ (0 <= limit) ” 
  &&  “ (limit <= len) ” 
  &&  “ (0 <= mirror) ” 
  &&  “ (mirror < len) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= maxId) ” 
  &&  “ (maxId < len) ” 
  &&  “ (0 < (i - r )) ” 
  &&  “ ((i + r ) < len) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_written)) = (i + 1 )) ” 
  &&  “ (ExpansionLoopState str s2_full len p_written i r id limit maxId maxLen ) ” 
  &&  “ (ExpansionAfterMatch s2_full len i r ) ”
  &&  (((( &( "p" ) ) + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i ( &( "p" ) ) i 0 (i + 1 ) p_written )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_full output_pre (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.undef_seg ( &( "p" ) ) (i + 1 ) 2003 )
.

Definition longestPalindrom_partial_solve_wit_16 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done: (@list Z)) (s2_full: (@list Z)) (out_prefix: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) ,
  “ (i <= (maxId + maxLen )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= i) ” 
  &&  “ (i <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i <= (maxId + maxLen )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= i) ” 
  &&  “ (i <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (((( &( "s2" ) ) + (i * sizeof(CHAR) ) )) # Char  |-> (Znth (i - 0 ) s2_full 0))
  **  (CharArray.missing_i ( &( "s2" ) ) i 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
.

Definition longestPalindrom_partial_solve_wit_17 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done: (@list Z)) (s2_full: (@list Z)) (out_prefix: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) ,
  “ ((Znth (i - 0 ) s2_full 0) <> 35) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i <= (maxId + maxLen )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= i) ” 
  &&  “ (i <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  “ ((Znth (i - 0 ) s2_full 0) <> 35) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i <= (maxId + maxLen )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= i) ” 
  &&  “ (i <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (((( &( "s2" ) ) + (i * sizeof(CHAR) ) )) # Char  |-> (Znth (i - 0 ) s2_full 0))
  **  (CharArray.missing_i ( &( "s2" ) ) i 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
.

Definition longestPalindrom_partial_solve_wit_18 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done: (@list Z)) (s2_full: (@list Z)) (out_prefix: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) ,
  “ ((Znth (i - 0 ) s2_full 0) <> 35) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i <= (maxId + maxLen )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= i) ” 
  &&  “ (i <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  “ ((Znth (i - 0 ) s2_full 0) <> 35) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i <= (maxId + maxLen )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= i) ” 
  &&  “ (i <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (((output_pre + (j * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i output_pre j j (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
.

Definition longestPalindrom_partial_solve_wit_19 := 
forall (output_pre: Z) (n_pre: Z) (s_pre: Z) (str: (@list Z)) (id: Z) (limit: Z) (p_done: (@list Z)) (s2_full: (@list Z)) (out_prefix: (@list Z)) (ret: Z) (mirror: Z) (r: Z) (j: Z) (i: Z) (maxId: Z) (maxLen: Z) (len: Z) ,
  “ (i > (maxId + maxLen )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= i) ” 
  &&  “ (i <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (store_string s_pre str )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.undef_seg output_pre j (n_pre + 1 ) )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
|--
  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (i > (maxId + maxLen )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (AlnumString str ) ” 
  &&  “ ((string_length (str)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (len = ((2 * n_pre ) + 2 )) ” 
  &&  “ (len <= 2002) ” 
  &&  “ (1 <= maxLen) ” 
  &&  “ (0 <= maxLen) ” 
  &&  “ (maxLen <= n_pre) ” 
  &&  “ (0 <= (maxId - maxLen )) ” 
  &&  “ ((maxId + maxLen ) < len) ” 
  &&  “ ((maxId - maxLen ) <= i) ” 
  &&  “ (i <= ((maxId + maxLen ) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= maxLen) ” 
  &&  “ (r = 0) ” 
  &&  “ (mirror = 0) ” 
  &&  “ (ret = 0) ” 
  &&  “ (OutputCopyPrefix s2_full out_prefix (maxId - maxLen ) i j ) ” 
  &&  “ forall (cur: Z) , ((((maxId - maxLen ) <= cur) /\ (cur <= ((maxId + maxLen ) + 1 ))) -> (OutputCopyBound s2_full (maxId - maxLen ) cur maxLen )) ” 
  &&  “ ((Zlength (s2_full)) = (len + 1 )) ” 
  &&  “ ((Zlength (p_done)) = len) ” 
  &&  “ (ManacherLoopState str s2_full len p_done len id limit maxId maxLen ) ”
  &&  (((output_pre + (j * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (str)) + 1 ) (c_string (str)) )
  **  (CharArray.undef_missing_i output_pre j j (n_pre + 1 ) )
  **  (CharArray.full output_pre j out_prefix )
  **  (CharArray.seg ( &( "s2" ) ) 0 (len + 1 ) s2_full )
  **  (CharArray.undef_seg ( &( "s2" ) ) (len + 1 ) 2003 )
  **  (IntArray.seg ( &( "p" ) ) 0 len p_done )
  **  (IntArray.undef_seg ( &( "p" ) ) len 2003 )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_longestPalindrom_safety_wit_1 : longestPalindrom_safety_wit_1.
Axiom proof_of_longestPalindrom_safety_wit_2 : longestPalindrom_safety_wit_2.
Axiom proof_of_longestPalindrom_safety_wit_3 : longestPalindrom_safety_wit_3.
Axiom proof_of_longestPalindrom_safety_wit_4 : longestPalindrom_safety_wit_4.
Axiom proof_of_longestPalindrom_safety_wit_5 : longestPalindrom_safety_wit_5.
Axiom proof_of_longestPalindrom_safety_wit_6 : longestPalindrom_safety_wit_6.
Axiom proof_of_longestPalindrom_safety_wit_7 : longestPalindrom_safety_wit_7.
Axiom proof_of_longestPalindrom_safety_wit_8 : longestPalindrom_safety_wit_8.
Axiom proof_of_longestPalindrom_safety_wit_9 : longestPalindrom_safety_wit_9.
Axiom proof_of_longestPalindrom_safety_wit_10 : longestPalindrom_safety_wit_10.
Axiom proof_of_longestPalindrom_safety_wit_11 : longestPalindrom_safety_wit_11.
Axiom proof_of_longestPalindrom_safety_wit_12 : longestPalindrom_safety_wit_12.
Axiom proof_of_longestPalindrom_safety_wit_13 : longestPalindrom_safety_wit_13.
Axiom proof_of_longestPalindrom_safety_wit_14 : longestPalindrom_safety_wit_14.
Axiom proof_of_longestPalindrom_safety_wit_15 : longestPalindrom_safety_wit_15.
Axiom proof_of_longestPalindrom_safety_wit_16 : longestPalindrom_safety_wit_16.
Axiom proof_of_longestPalindrom_safety_wit_17 : longestPalindrom_safety_wit_17.
Axiom proof_of_longestPalindrom_safety_wit_18 : longestPalindrom_safety_wit_18.
Axiom proof_of_longestPalindrom_safety_wit_19 : longestPalindrom_safety_wit_19.
Axiom proof_of_longestPalindrom_safety_wit_20 : longestPalindrom_safety_wit_20.
Axiom proof_of_longestPalindrom_safety_wit_21 : longestPalindrom_safety_wit_21.
Axiom proof_of_longestPalindrom_safety_wit_22 : longestPalindrom_safety_wit_22.
Axiom proof_of_longestPalindrom_safety_wit_23 : longestPalindrom_safety_wit_23.
Axiom proof_of_longestPalindrom_safety_wit_24 : longestPalindrom_safety_wit_24.
Axiom proof_of_longestPalindrom_safety_wit_25 : longestPalindrom_safety_wit_25.
Axiom proof_of_longestPalindrom_safety_wit_26 : longestPalindrom_safety_wit_26.
Axiom proof_of_longestPalindrom_safety_wit_27 : longestPalindrom_safety_wit_27.
Axiom proof_of_longestPalindrom_safety_wit_28 : longestPalindrom_safety_wit_28.
Axiom proof_of_longestPalindrom_safety_wit_29 : longestPalindrom_safety_wit_29.
Axiom proof_of_longestPalindrom_safety_wit_30 : longestPalindrom_safety_wit_30.
Axiom proof_of_longestPalindrom_safety_wit_31 : longestPalindrom_safety_wit_31.
Axiom proof_of_longestPalindrom_safety_wit_32 : longestPalindrom_safety_wit_32.
Axiom proof_of_longestPalindrom_safety_wit_33 : longestPalindrom_safety_wit_33.
Axiom proof_of_longestPalindrom_safety_wit_34 : longestPalindrom_safety_wit_34.
Axiom proof_of_longestPalindrom_safety_wit_35 : longestPalindrom_safety_wit_35.
Axiom proof_of_longestPalindrom_safety_wit_36 : longestPalindrom_safety_wit_36.
Axiom proof_of_longestPalindrom_safety_wit_37 : longestPalindrom_safety_wit_37.
Axiom proof_of_longestPalindrom_safety_wit_38 : longestPalindrom_safety_wit_38.
Axiom proof_of_longestPalindrom_safety_wit_39 : longestPalindrom_safety_wit_39.
Axiom proof_of_longestPalindrom_safety_wit_40 : longestPalindrom_safety_wit_40.
Axiom proof_of_longestPalindrom_safety_wit_41 : longestPalindrom_safety_wit_41.
Axiom proof_of_longestPalindrom_safety_wit_42 : longestPalindrom_safety_wit_42.
Axiom proof_of_longestPalindrom_safety_wit_43 : longestPalindrom_safety_wit_43.
Axiom proof_of_longestPalindrom_safety_wit_44 : longestPalindrom_safety_wit_44.
Axiom proof_of_longestPalindrom_safety_wit_45 : longestPalindrom_safety_wit_45.
Axiom proof_of_longestPalindrom_safety_wit_46 : longestPalindrom_safety_wit_46.
Axiom proof_of_longestPalindrom_safety_wit_47 : longestPalindrom_safety_wit_47.
Axiom proof_of_longestPalindrom_safety_wit_48 : longestPalindrom_safety_wit_48.
Axiom proof_of_longestPalindrom_safety_wit_49 : longestPalindrom_safety_wit_49.
Axiom proof_of_longestPalindrom_safety_wit_50 : longestPalindrom_safety_wit_50.
Axiom proof_of_longestPalindrom_safety_wit_51 : longestPalindrom_safety_wit_51.
Axiom proof_of_longestPalindrom_safety_wit_52 : longestPalindrom_safety_wit_52.
Axiom proof_of_longestPalindrom_safety_wit_53 : longestPalindrom_safety_wit_53.
Axiom proof_of_longestPalindrom_safety_wit_54 : longestPalindrom_safety_wit_54.
Axiom proof_of_longestPalindrom_safety_wit_55 : longestPalindrom_safety_wit_55.
Axiom proof_of_longestPalindrom_safety_wit_56 : longestPalindrom_safety_wit_56.
Axiom proof_of_longestPalindrom_safety_wit_57 : longestPalindrom_safety_wit_57.
Axiom proof_of_longestPalindrom_safety_wit_58 : longestPalindrom_safety_wit_58.
Axiom proof_of_longestPalindrom_safety_wit_59 : longestPalindrom_safety_wit_59.
Axiom proof_of_longestPalindrom_safety_wit_60 : longestPalindrom_safety_wit_60.
Axiom proof_of_longestPalindrom_safety_wit_61 : longestPalindrom_safety_wit_61.
Axiom proof_of_longestPalindrom_safety_wit_62 : longestPalindrom_safety_wit_62.
Axiom proof_of_longestPalindrom_safety_wit_63 : longestPalindrom_safety_wit_63.
Axiom proof_of_longestPalindrom_safety_wit_64 : longestPalindrom_safety_wit_64.
Axiom proof_of_longestPalindrom_safety_wit_65 : longestPalindrom_safety_wit_65.
Axiom proof_of_longestPalindrom_safety_wit_66 : longestPalindrom_safety_wit_66.
Axiom proof_of_longestPalindrom_safety_wit_67 : longestPalindrom_safety_wit_67.
Axiom proof_of_longestPalindrom_safety_wit_68 : longestPalindrom_safety_wit_68.
Axiom proof_of_longestPalindrom_safety_wit_69 : longestPalindrom_safety_wit_69.
Axiom proof_of_longestPalindrom_safety_wit_70 : longestPalindrom_safety_wit_70.
Axiom proof_of_longestPalindrom_safety_wit_71 : longestPalindrom_safety_wit_71.
Axiom proof_of_longestPalindrom_safety_wit_72 : longestPalindrom_safety_wit_72.
Axiom proof_of_longestPalindrom_safety_wit_73 : longestPalindrom_safety_wit_73.
Axiom proof_of_longestPalindrom_safety_wit_74 : longestPalindrom_safety_wit_74.
Axiom proof_of_longestPalindrom_entail_wit_1 : longestPalindrom_entail_wit_1.
Axiom proof_of_longestPalindrom_entail_wit_2 : longestPalindrom_entail_wit_2.
Axiom proof_of_longestPalindrom_entail_wit_3 : longestPalindrom_entail_wit_3.
Axiom proof_of_longestPalindrom_entail_wit_4 : longestPalindrom_entail_wit_4.
Axiom proof_of_longestPalindrom_entail_wit_5 : longestPalindrom_entail_wit_5.
Axiom proof_of_longestPalindrom_entail_wit_6_1 : longestPalindrom_entail_wit_6_1.
Axiom proof_of_longestPalindrom_entail_wit_6_2 : longestPalindrom_entail_wit_6_2.
Axiom proof_of_longestPalindrom_entail_wit_6_3 : longestPalindrom_entail_wit_6_3.
Axiom proof_of_longestPalindrom_entail_wit_7 : longestPalindrom_entail_wit_7.
Axiom proof_of_longestPalindrom_entail_wit_8 : longestPalindrom_entail_wit_8.
Axiom proof_of_longestPalindrom_entail_wit_9 : longestPalindrom_entail_wit_9.
Axiom proof_of_longestPalindrom_entail_wit_10_1 : longestPalindrom_entail_wit_10_1.
Axiom proof_of_longestPalindrom_entail_wit_10_2 : longestPalindrom_entail_wit_10_2.
Axiom proof_of_longestPalindrom_entail_wit_10_3 : longestPalindrom_entail_wit_10_3.
Axiom proof_of_longestPalindrom_entail_wit_10_4 : longestPalindrom_entail_wit_10_4.
Axiom proof_of_longestPalindrom_entail_wit_11 : longestPalindrom_entail_wit_11.
Axiom proof_of_longestPalindrom_entail_wit_12 : longestPalindrom_entail_wit_12.
Axiom proof_of_longestPalindrom_entail_wit_13 : longestPalindrom_entail_wit_13.
Axiom proof_of_longestPalindrom_entail_wit_14_1 : longestPalindrom_entail_wit_14_1.
Axiom proof_of_longestPalindrom_entail_wit_14_2 : longestPalindrom_entail_wit_14_2.
Axiom proof_of_longestPalindrom_entail_wit_15 : longestPalindrom_entail_wit_15.
Axiom proof_of_longestPalindrom_return_wit_1 : longestPalindrom_return_wit_1.
Axiom proof_of_longestPalindrom_partial_solve_wit_1 : longestPalindrom_partial_solve_wit_1.
Axiom proof_of_longestPalindrom_partial_solve_wit_2 : longestPalindrom_partial_solve_wit_2.
Axiom proof_of_longestPalindrom_partial_solve_wit_3 : longestPalindrom_partial_solve_wit_3.
Axiom proof_of_longestPalindrom_partial_solve_wit_4 : longestPalindrom_partial_solve_wit_4.
Axiom proof_of_longestPalindrom_partial_solve_wit_5 : longestPalindrom_partial_solve_wit_5.
Axiom proof_of_longestPalindrom_partial_solve_wit_6 : longestPalindrom_partial_solve_wit_6.
Axiom proof_of_longestPalindrom_partial_solve_wit_7 : longestPalindrom_partial_solve_wit_7.
Axiom proof_of_longestPalindrom_partial_solve_wit_8 : longestPalindrom_partial_solve_wit_8.
Axiom proof_of_longestPalindrom_partial_solve_wit_9 : longestPalindrom_partial_solve_wit_9.
Axiom proof_of_longestPalindrom_partial_solve_wit_10 : longestPalindrom_partial_solve_wit_10.
Axiom proof_of_longestPalindrom_partial_solve_wit_11 : longestPalindrom_partial_solve_wit_11.
Axiom proof_of_longestPalindrom_partial_solve_wit_12 : longestPalindrom_partial_solve_wit_12.
Axiom proof_of_longestPalindrom_partial_solve_wit_13 : longestPalindrom_partial_solve_wit_13.
Axiom proof_of_longestPalindrom_partial_solve_wit_14 : longestPalindrom_partial_solve_wit_14.
Axiom proof_of_longestPalindrom_partial_solve_wit_15 : longestPalindrom_partial_solve_wit_15.
Axiom proof_of_longestPalindrom_partial_solve_wit_16 : longestPalindrom_partial_solve_wit_16.
Axiom proof_of_longestPalindrom_partial_solve_wit_17 : longestPalindrom_partial_solve_wit_17.
Axiom proof_of_longestPalindrom_partial_solve_wit_18 : longestPalindrom_partial_solve_wit_18.
Axiom proof_of_longestPalindrom_partial_solve_wit_19 : longestPalindrom_partial_solve_wit_19.

End VC_Correct.
