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
Require Import SimpleC.EE.LLM_bench.Engineering.string.strcmp_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
Require Import string_strategy_goal.
Require Import string_strategy_proof.

(*----- Function strcmp -----*)

Definition strcmp_safety_wit_1 := 
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) ,
  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strcmp_safety_wit_2 := 
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) ,
  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (str1))) ” 
  &&  “ (i <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strcmp_safety_wit_3 := 
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (str1)) 0) = (Znth i (c_string (str2)) 0)) ” 
  &&  “ ((Znth i (c_string (str1)) 0) <> 0) ” 
  &&  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (str1))) ” 
  &&  “ (i <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition strcmp_safety_wit_4 := 
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (str1)) 0) = 0) ” 
  &&  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (str1))) ” 
  &&  “ (i <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) )) ”
.

Definition strcmp_safety_wit_5 := 
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (str1)) 0) <> (Znth i (c_string (str2)) 0)) ” 
  &&  “ ((Znth i (c_string (str1)) 0) <> 0) ” 
  &&  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (str1))) ” 
  &&  “ (i <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) )) ”
.

Definition strcmp_entail_wit_1 := 
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) ,
  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (string_length (str1))) ” 
  &&  “ (0 <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
.

Definition strcmp_entail_wit_2 := 
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (str1)) 0) = (Znth i (c_string (str2)) 0)) ” 
  &&  “ ((Znth i (c_string (str1)) 0) <> 0) ” 
  &&  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (str1))) ” 
  &&  “ (i <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (string_length (str1))) ” 
  &&  “ ((i + 1 ) <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
.

Definition strcmp_return_wit_1 := 
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (str1)) 0) = 0) ” 
  &&  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (str1))) ” 
  &&  “ (i <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (strcmp_result str1 str2 ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) ) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
.

Definition strcmp_return_wit_2 := 
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (str1)) 0) <> (Znth i (c_string (str2)) 0)) ” 
  &&  “ ((Znth i (c_string (str1)) 0) <> 0) ” 
  &&  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (str1))) ” 
  &&  “ (i <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (strcmp_result str1 str2 ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) ) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
.

(*----- Function strncmp -----*)

Definition strncmp_safety_wit_1 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) ,
  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strncmp_safety_wit_2 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i <= (string_length (str1))) ” 
  &&  “ (i <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strncmp_safety_wit_3 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (str1)) 0) = (Znth i (c_string (str2)) 0)) ” 
  &&  “ ((Znth i (c_string (str1)) 0) <> 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i <= (string_length (str1))) ” 
  &&  “ (i <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition strncmp_safety_wit_4 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) ,
  “ (i = n_pre) ” 
  &&  “ ((Znth i (c_string (str1)) 0) <> (Znth i (c_string (str2)) 0)) ” 
  &&  “ ((Znth i (c_string (str1)) 0) <> 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i <= (string_length (str1))) ” 
  &&  “ (i <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ False ”
.

Definition strncmp_safety_wit_5 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) ,
  “ (i <> n_pre) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i <= (string_length (str1))) ” 
  &&  “ (i <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ False ”
.

Definition strncmp_safety_wit_6 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) ,
  “ (i = n_pre) ” 
  &&  “ ((Znth i (c_string (str1)) 0) = 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i <= (string_length (str1))) ” 
  &&  “ (i <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ False ”
.

Definition strncmp_safety_wit_7 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) ,
  “ (i = n_pre) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i <= (string_length (str1))) ” 
  &&  “ (i <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strncmp_safety_wit_8 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) ,
  “ (i <> n_pre) ” 
  &&  “ ((Znth i (c_string (str1)) 0) <> (Znth i (c_string (str2)) 0)) ” 
  &&  “ ((Znth i (c_string (str1)) 0) <> 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i <= (string_length (str1))) ” 
  &&  “ (i <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) )) ”
.

Definition strncmp_safety_wit_9 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) ,
  “ (i <> n_pre) ” 
  &&  “ ((Znth i (c_string (str1)) 0) = 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i <= (string_length (str1))) ” 
  &&  “ (i <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) )) ”
.

Definition strncmp_entail_wit_1 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) ,
  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= (string_length (str1))) ” 
  &&  “ (0 <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
.

Definition strncmp_entail_wit_2 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (str1)) 0) = (Znth i (c_string (str2)) 0)) ” 
  &&  “ ((Znth i (c_string (str1)) 0) <> 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i <= (string_length (str1))) ” 
  &&  “ (i <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((i + 1 ) <= (string_length (str1))) ” 
  &&  “ ((i + 1 ) <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
.

Definition strncmp_return_wit_1 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) ,
  “ (i <> n_pre) ” 
  &&  “ ((Znth i (c_string (str1)) 0) <> (Znth i (c_string (str2)) 0)) ” 
  &&  “ ((Znth i (c_string (str1)) 0) <> 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i <= (string_length (str1))) ” 
  &&  “ (i <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (strncmp_result str1 str2 n_pre ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) ) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
.

Definition strncmp_return_wit_2 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) ,
  “ (i <> n_pre) ” 
  &&  “ ((Znth i (c_string (str1)) 0) = 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i <= (string_length (str1))) ” 
  &&  “ (i <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (strncmp_result str1 str2 n_pre ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) ) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
.

Definition strncmp_return_wit_3 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) ,
  “ (i = n_pre) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i <= (string_length (str1))) ” 
  &&  “ (i <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (strncmp_result str1 str2 n_pre 0 ) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_strcmp_safety_wit_1 : strcmp_safety_wit_1.
Axiom proof_of_strcmp_safety_wit_2 : strcmp_safety_wit_2.
Axiom proof_of_strcmp_safety_wit_3 : strcmp_safety_wit_3.
Axiom proof_of_strcmp_safety_wit_4 : strcmp_safety_wit_4.
Axiom proof_of_strcmp_safety_wit_5 : strcmp_safety_wit_5.
Axiom proof_of_strcmp_entail_wit_1 : strcmp_entail_wit_1.
Axiom proof_of_strcmp_entail_wit_2 : strcmp_entail_wit_2.
Axiom proof_of_strcmp_return_wit_1 : strcmp_return_wit_1.
Axiom proof_of_strcmp_return_wit_2 : strcmp_return_wit_2.
Axiom proof_of_strncmp_safety_wit_1 : strncmp_safety_wit_1.
Axiom proof_of_strncmp_safety_wit_2 : strncmp_safety_wit_2.
Axiom proof_of_strncmp_safety_wit_3 : strncmp_safety_wit_3.
Axiom proof_of_strncmp_safety_wit_4 : strncmp_safety_wit_4.
Axiom proof_of_strncmp_safety_wit_5 : strncmp_safety_wit_5.
Axiom proof_of_strncmp_safety_wit_6 : strncmp_safety_wit_6.
Axiom proof_of_strncmp_safety_wit_7 : strncmp_safety_wit_7.
Axiom proof_of_strncmp_safety_wit_8 : strncmp_safety_wit_8.
Axiom proof_of_strncmp_safety_wit_9 : strncmp_safety_wit_9.
Axiom proof_of_strncmp_entail_wit_1 : strncmp_entail_wit_1.
Axiom proof_of_strncmp_entail_wit_2 : strncmp_entail_wit_2.
Axiom proof_of_strncmp_return_wit_1 : strncmp_return_wit_1.
Axiom proof_of_strncmp_return_wit_2 : strncmp_return_wit_2.
Axiom proof_of_strncmp_return_wit_3 : strncmp_return_wit_3.

End VC_Correct.
