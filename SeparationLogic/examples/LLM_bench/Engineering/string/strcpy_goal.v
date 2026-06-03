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
Require Import SimpleC.EE.LLM_bench.Engineering.string.strcpy_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
Require Import string_strategy_goal.
Require Import string_strategy_proof.

(*----- Function strcpy -----*)

Definition strcpy_safety_wit_1 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) ,
  “ (valid_string src_str ) ” 
  &&  “ ((string_length (src_str)) < INT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  (CharArray.undef_full dest_pre ((string_length (src_str)) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strcpy_safety_wit_2 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) ,
  “ (valid_string src_str ) ” 
  &&  “ ((string_length (src_str)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (src_str))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (CharArray.full dest_pre i (sublist (0) (i) (src_str)) )
  **  (CharArray.undef_seg dest_pre i ((string_length (src_str)) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strcpy_safety_wit_3 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) ,
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ ((Znth i (c_string (src_str)) 0) <> 0) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((string_length (src_str)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre (i + 1 ) (app ((sublist (0) (i) (src_str))) ((cons ((Znth i (c_string (src_str)) 0)) (nil)))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) ((string_length (src_str)) + 1 ) )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition strcpy_safety_wit_4 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (src_str)) 0) = 0) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((string_length (src_str)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (src_str))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (CharArray.full dest_pre i (sublist (0) (i) (src_str)) )
  **  (CharArray.undef_seg dest_pre i ((string_length (src_str)) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strcpy_entail_wit_1 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) ,
  “ (valid_string src_str ) ” 
  &&  “ ((string_length (src_str)) < INT_MAX) ”
  &&  (CharArray.undef_full dest_pre ((string_length (src_str)) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (valid_string src_str ) ” 
  &&  “ ((string_length (src_str)) < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre 0 (sublist (0) (0) (src_str)) )
  **  (CharArray.undef_seg dest_pre 0 ((string_length (src_str)) + 1 ) )
  **  (store_string src_pre src_str )
.

Definition strcpy_entail_wit_2 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) ,
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ ((Znth i (c_string (src_str)) 0) <> 0) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((string_length (src_str)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre (i + 1 ) (app ((sublist (0) (i) (src_str))) ((cons ((Znth i (c_string (src_str)) 0)) (nil)))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) ((string_length (src_str)) + 1 ) )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
|--
  “ (valid_string src_str ) ” 
  &&  “ ((string_length (src_str)) < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre (i + 1 ) (sublist (0) ((i + 1 )) (src_str)) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) ((string_length (src_str)) + 1 ) )
  **  (store_string src_pre src_str )
.

Definition strcpy_return_wit_1 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) ,
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ ((Znth i (c_string (src_str)) 0) = 0) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((string_length (src_str)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre (i + 1 ) (app ((sublist (0) (i) (src_str))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) ((string_length (src_str)) + 1 ) )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
|--
  “ (dest_pre = dest_pre) ”
  &&  (store_string dest_pre src_str )
  **  (store_string src_pre src_str )
.

Definition strcpy_partial_solve_wit_1 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (src_str)) 0) <> 0) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((string_length (src_str)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre i (sublist (0) (i) (src_str)) )
  **  (CharArray.undef_seg dest_pre i ((string_length (src_str)) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ ((Znth i (c_string (src_str)) 0) <> 0) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((string_length (src_str)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (src_str))) ”
  &&  (((dest_pre + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  (CharArray.undef_missing_i dest_pre i i ((string_length (src_str)) + 1 ) )
  **  (CharArray.full dest_pre i (sublist (0) (i) (src_str)) )
.

Definition strcpy_partial_solve_wit_2 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (src_str)) 0) = 0) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((string_length (src_str)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre i (sublist (0) (i) (src_str)) )
  **  (CharArray.undef_seg dest_pre i ((string_length (src_str)) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ ((Znth i (c_string (src_str)) 0) = 0) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((string_length (src_str)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (src_str))) ”
  &&  (((dest_pre + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  (CharArray.undef_missing_i dest_pre i i ((string_length (src_str)) + 1 ) )
  **  (CharArray.full dest_pre i (sublist (0) (i) (src_str)) )
.

(*----- Function strncpy -----*)

Definition strncpy_safety_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) ,
  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  (CharArray.undef_full dest_pre n_pre )
  **  (store_string src_pre src_str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strncpy_safety_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i <= (string_length (src_str))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full dest_pre i (sublist (0) (i) (src_str)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (store_string src_pre src_str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strncpy_safety_wit_3 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) ,
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ ((Znth i (c_string (src_str)) 0) <> 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre (i + 1 ) (app ((sublist (0) (i) (src_str))) ((cons ((Znth i (c_string (src_str)) 0)) (nil)))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition strncpy_safety_wit_4 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (out: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (strncpy_content src_str i out ) ” 
  &&  “ ((i < n_pre) -> ((string_length (src_str)) <= i)) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full dest_pre i out )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (store_string src_pre src_str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strncpy_safety_wit_5 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (out: (@list Z)) (i: Z) ,
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (strncpy_content src_str i out ) ” 
  &&  “ ((i < n_pre) -> ((string_length (src_str)) <= i)) ”
  &&  (CharArray.full dest_pre (i + 1 ) (app (out) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition strncpy_entail_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) ,
  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (CharArray.undef_full dest_pre n_pre )
  **  (store_string src_pre src_str )
|--
  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre 0 (sublist (0) (0) (src_str)) )
  **  (CharArray.undef_seg dest_pre 0 n_pre )
  **  (store_string src_pre src_str )
.

Definition strncpy_entail_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) ,
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ ((Znth i (c_string (src_str)) 0) <> 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre (i + 1 ) (app ((sublist (0) (i) (src_str))) ((cons ((Znth i (c_string (src_str)) 0)) (nil)))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
|--
  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((i + 1 ) <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre (i + 1 ) (sublist (0) ((i + 1 )) (src_str)) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (store_string src_pre src_str )
.

Definition strncpy_entail_wit_3_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (src_str)) 0) = 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre i (sublist (0) (i) (src_str)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (store_string src_pre src_str )
|--
  EX (out: (@list Z)) ,
  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (strncpy_content src_str i out ) ” 
  &&  “ ((i < n_pre) -> ((string_length (src_str)) <= i)) ”
  &&  (CharArray.full dest_pre i out )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (store_string src_pre src_str )
.

Definition strncpy_entail_wit_3_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre i (sublist (0) (i) (src_str)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (store_string src_pre src_str )
|--
  EX (out: (@list Z)) ,
  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (strncpy_content src_str i out ) ” 
  &&  “ ((i < n_pre) -> ((string_length (src_str)) <= i)) ”
  &&  (CharArray.full dest_pre i out )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (store_string src_pre src_str )
.

Definition strncpy_entail_wit_4 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (out_2: (@list Z)) (i: Z) ,
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (strncpy_content src_str i out_2 ) ” 
  &&  “ ((i < n_pre) -> ((string_length (src_str)) <= i)) ”
  &&  (CharArray.full dest_pre (i + 1 ) (app (out_2) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
|--
  EX (out: (@list Z)) ,
  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (strncpy_content src_str (i + 1 ) out ) ” 
  &&  “ (((i + 1 ) < n_pre) -> ((string_length (src_str)) <= (i + 1 ))) ”
  &&  (CharArray.full dest_pre (i + 1 ) out )
  **  (CharArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (store_string src_pre src_str )
.

Definition strncpy_return_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (out_2: (@list Z)) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (strncpy_content src_str i out_2 ) ” 
  &&  “ ((i < n_pre) -> ((string_length (src_str)) <= i)) ”
  &&  (CharArray.full dest_pre i out_2 )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (store_string src_pre src_str )
|--
  EX (out: (@list Z)) ,
  “ (strncpy_content src_str n_pre out ) ” 
  &&  “ (dest_pre = dest_pre) ”
  &&  (CharArray.full dest_pre n_pre out )
  **  (store_string src_pre src_str )
.

Definition strncpy_partial_solve_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (src_str)) 0) <> 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre i (sublist (0) (i) (src_str)) )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (store_string src_pre src_str )
|--
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ ((Znth i (c_string (src_str)) 0) <> 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i <= (string_length (src_str))) ”
  &&  (((dest_pre + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  (CharArray.undef_missing_i dest_pre i i n_pre )
  **  (CharArray.full dest_pre i (sublist (0) (i) (src_str)) )
.

Definition strncpy_partial_solve_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (out: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (strncpy_content src_str i out ) ” 
  &&  “ ((i < n_pre) -> ((string_length (src_str)) <= i)) ”
  &&  (CharArray.full dest_pre i out )
  **  (CharArray.undef_seg dest_pre i n_pre )
  **  (store_string src_pre src_str )
|--
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (strncpy_content src_str i out ) ” 
  &&  “ ((i < n_pre) -> ((string_length (src_str)) <= i)) ”
  &&  (((dest_pre + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  (CharArray.undef_missing_i dest_pre i i n_pre )
  **  (CharArray.full dest_pre i out )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_strcpy_safety_wit_1 : strcpy_safety_wit_1.
Axiom proof_of_strcpy_safety_wit_2 : strcpy_safety_wit_2.
Axiom proof_of_strcpy_safety_wit_3 : strcpy_safety_wit_3.
Axiom proof_of_strcpy_safety_wit_4 : strcpy_safety_wit_4.
Axiom proof_of_strcpy_entail_wit_1 : strcpy_entail_wit_1.
Axiom proof_of_strcpy_entail_wit_2 : strcpy_entail_wit_2.
Axiom proof_of_strcpy_return_wit_1 : strcpy_return_wit_1.
Axiom proof_of_strcpy_partial_solve_wit_1 : strcpy_partial_solve_wit_1.
Axiom proof_of_strcpy_partial_solve_wit_2 : strcpy_partial_solve_wit_2.
Axiom proof_of_strncpy_safety_wit_1 : strncpy_safety_wit_1.
Axiom proof_of_strncpy_safety_wit_2 : strncpy_safety_wit_2.
Axiom proof_of_strncpy_safety_wit_3 : strncpy_safety_wit_3.
Axiom proof_of_strncpy_safety_wit_4 : strncpy_safety_wit_4.
Axiom proof_of_strncpy_safety_wit_5 : strncpy_safety_wit_5.
Axiom proof_of_strncpy_entail_wit_1 : strncpy_entail_wit_1.
Axiom proof_of_strncpy_entail_wit_2 : strncpy_entail_wit_2.
Axiom proof_of_strncpy_entail_wit_3_1 : strncpy_entail_wit_3_1.
Axiom proof_of_strncpy_entail_wit_3_2 : strncpy_entail_wit_3_2.
Axiom proof_of_strncpy_entail_wit_4 : strncpy_entail_wit_4.
Axiom proof_of_strncpy_return_wit_1 : strncpy_return_wit_1.
Axiom proof_of_strncpy_partial_solve_wit_1 : strncpy_partial_solve_wit_1.
Axiom proof_of_strncpy_partial_solve_wit_2 : strncpy_partial_solve_wit_2.

End VC_Correct.
