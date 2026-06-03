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
Require Import SimpleC.EE.LLM_bench.Engineering.string.search_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
Require Import string_strategy_goal.
Require Import string_strategy_proof.

(*----- Function memchr -----*)

Definition memchr_safety_wit_1 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (bytes: (@list Z)) ,
  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre n_pre bytes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition memchr_safety_wit_2 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (bytes: (@list Z)) (i: Z) ,
  “ ((Znth i bytes 0) <> c_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre)) ”
  &&  (CharArray.full s_pre n_pre bytes )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition memchr_safety_wit_3 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (bytes: (@list Z)) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre)) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full s_pre n_pre bytes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition memchr_entail_wit_1 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (bytes: (@list Z)) ,
  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (CharArray.full s_pre n_pre bytes )
|--
  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) (bytes) (0)) <> c_pre)) ”
  &&  (CharArray.full s_pre n_pre bytes )
.

Definition memchr_entail_wit_2 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (bytes: (@list Z)) (i: Z) ,
  “ ((Znth i bytes 0) <> c_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre)) ”
  &&  (CharArray.full s_pre n_pre bytes )
|--
  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (bytes) (0)) <> c_pre)) ”
  &&  (CharArray.full s_pre n_pre bytes )
.

Definition memchr_return_wit_1 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (bytes: (@list Z)) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre)) ”
  &&  (CharArray.full s_pre n_pre bytes )
|--
  “ (memchr_result bytes c_pre n_pre 0 s_pre ) ”
  &&  (CharArray.full s_pre n_pre bytes )
.

Definition memchr_return_wit_2 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (bytes: (@list Z)) (i: Z) ,
  “ ((Znth i bytes 0) = c_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre)) ”
  &&  (CharArray.full s_pre n_pre bytes )
|--
  “ (memchr_result bytes c_pre n_pre (s_pre + (i * sizeof(CHAR) ) ) s_pre ) ”
  &&  (CharArray.full s_pre n_pre bytes )
.

Definition memchr_partial_solve_wit_1 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (bytes: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre)) ”
  &&  (CharArray.full s_pre n_pre bytes )
|--
  “ (i < n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre)) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i bytes 0))
  **  (CharArray.missing_i s_pre i 0 n_pre bytes )
.

(*----- Function strchr -----*)

Definition strchr_safety_wit_1 := 
forall (c_pre: Z) (s_pre: Z) (str: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ ((string_length (str)) < INT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strchr_safety_wit_2 := 
forall (c_pre: Z) (s_pre: Z) (str: (@list Z)) (i: Z) ,
  “ (valid_string str ) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ ((string_length (str)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre)) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  (store_string s_pre str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strchr_safety_wit_3 := 
forall (c_pre: Z) (s_pre: Z) (str: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (str)) 0) <> c_pre) ” 
  &&  “ ((Znth i (c_string (str)) 0) <> 0) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ ((string_length (str)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre)) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  (store_string s_pre str )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition strchr_safety_wit_4 := 
forall (c_pre: Z) (s_pre: Z) (str: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (str)) 0) = 0) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ ((string_length (str)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre)) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  (store_string s_pre str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strchr_safety_wit_5 := 
forall (c_pre: Z) (s_pre: Z) (str: (@list Z)) (i: Z) ,
  “ (c_pre <> 0) ” 
  &&  “ ((Znth i (c_string (str)) 0) = 0) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ ((string_length (str)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre)) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  (store_string s_pre str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strchr_entail_wit_1 := 
forall (c_pre: Z) (s_pre: Z) (str: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ ((string_length (str)) < INT_MAX) ”
  &&  (store_string s_pre str )
|--
  “ (valid_string str ) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ ((string_length (str)) < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (string_length (str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) (str) (0)) <> c_pre)) ”
  &&  (store_string s_pre str )
.

Definition strchr_entail_wit_2 := 
forall (c_pre: Z) (s_pre: Z) (str: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (str)) 0) <> c_pre) ” 
  &&  “ ((Znth i (c_string (str)) 0) <> 0) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ ((string_length (str)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre)) ”
  &&  (store_string s_pre str )
|--
  “ (valid_string str ) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ ((string_length (str)) < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (string_length (str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (str) (0)) <> c_pre)) ”
  &&  (store_string s_pre str )
.

Definition strchr_return_wit_1 := 
forall (c_pre: Z) (s_pre: Z) (str: (@list Z)) (i: Z) ,
  “ (c_pre <> 0) ” 
  &&  “ ((Znth i (c_string (str)) 0) = 0) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ ((string_length (str)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre)) ”
  &&  (store_string s_pre str )
|--
  “ (strchr_result str c_pre 0 s_pre ) ”
  &&  (store_string s_pre str )
.

Definition strchr_return_wit_2 := 
forall (c_pre: Z) (s_pre: Z) (str: (@list Z)) (i: Z) ,
  “ (c_pre = 0) ” 
  &&  “ ((Znth i (c_string (str)) 0) = 0) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ ((string_length (str)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre)) ”
  &&  (store_string s_pre str )
|--
  “ (strchr_result str c_pre (s_pre + (i * sizeof(CHAR) ) ) s_pre ) ”
  &&  (store_string s_pre str )
.

Definition strchr_return_wit_3 := 
forall (c_pre: Z) (s_pre: Z) (str: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (str)) 0) = c_pre) ” 
  &&  “ ((Znth i (c_string (str)) 0) <> 0) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ ((string_length (str)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre)) ”
  &&  (store_string s_pre str )
|--
  “ (strchr_result str c_pre (s_pre + (i * sizeof(CHAR) ) ) s_pre ) ”
  &&  (store_string s_pre str )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_memchr_safety_wit_1 : memchr_safety_wit_1.
Axiom proof_of_memchr_safety_wit_2 : memchr_safety_wit_2.
Axiom proof_of_memchr_safety_wit_3 : memchr_safety_wit_3.
Axiom proof_of_memchr_entail_wit_1 : memchr_entail_wit_1.
Axiom proof_of_memchr_entail_wit_2 : memchr_entail_wit_2.
Axiom proof_of_memchr_return_wit_1 : memchr_return_wit_1.
Axiom proof_of_memchr_return_wit_2 : memchr_return_wit_2.
Axiom proof_of_memchr_partial_solve_wit_1 : memchr_partial_solve_wit_1.
Axiom proof_of_strchr_safety_wit_1 : strchr_safety_wit_1.
Axiom proof_of_strchr_safety_wit_2 : strchr_safety_wit_2.
Axiom proof_of_strchr_safety_wit_3 : strchr_safety_wit_3.
Axiom proof_of_strchr_safety_wit_4 : strchr_safety_wit_4.
Axiom proof_of_strchr_safety_wit_5 : strchr_safety_wit_5.
Axiom proof_of_strchr_entail_wit_1 : strchr_entail_wit_1.
Axiom proof_of_strchr_entail_wit_2 : strchr_entail_wit_2.
Axiom proof_of_strchr_return_wit_1 : strchr_return_wit_1.
Axiom proof_of_strchr_return_wit_2 : strchr_return_wit_2.
Axiom proof_of_strchr_return_wit_3 : strchr_return_wit_3.

End VC_Correct.
