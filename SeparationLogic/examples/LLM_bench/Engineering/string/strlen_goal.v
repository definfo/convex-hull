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

(*----- Function strlen -----*)

Definition strlen_safety_wit_1 := 
forall (s_pre: Z) (str: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ ((string_length (str)) < INT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strlen_safety_wit_2 := 
forall (s_pre: Z) (str: (@list Z)) (i: Z) ,
  “ (valid_string str ) ” 
  &&  “ ((string_length (str)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strlen_safety_wit_3 := 
forall (s_pre: Z) (str: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (str)) 0) <> 0) ” 
  &&  “ (valid_string str ) ” 
  &&  “ ((string_length (str)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition strlen_entail_wit_1 := 
forall (s_pre: Z) (str: (@list Z)) ,
  “ (valid_string str ) ” 
  &&  “ ((string_length (str)) < INT_MAX) ”
  &&  (store_string s_pre str )
|--
  “ (valid_string str ) ” 
  &&  “ ((string_length (str)) < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (string_length (str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) (str) (0)) <> 0)) ”
  &&  (store_string s_pre str )
.

Definition strlen_entail_wit_2 := 
forall (s_pre: Z) (str: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (str)) 0) <> 0) ” 
  &&  “ (valid_string str ) ” 
  &&  “ ((string_length (str)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> 0)) ”
  &&  (store_string s_pre str )
|--
  “ (valid_string str ) ” 
  &&  “ ((string_length (str)) < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (string_length (str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (str) (0)) <> 0)) ”
  &&  (store_string s_pre str )
.

Definition strlen_return_wit_1 := 
forall (s_pre: Z) (str: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (str)) 0) = 0) ” 
  &&  “ (valid_string str ) ” 
  &&  “ ((string_length (str)) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> 0)) ”
  &&  (store_string s_pre str )
|--
  “ (i = (string_length (str))) ”
  &&  (store_string s_pre str )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_strlen_safety_wit_1 : strlen_safety_wit_1.
Axiom proof_of_strlen_safety_wit_2 : strlen_safety_wit_2.
Axiom proof_of_strlen_safety_wit_3 : strlen_safety_wit_3.
Axiom proof_of_strlen_entail_wit_1 : strlen_entail_wit_1.
Axiom proof_of_strlen_entail_wit_2 : strlen_entail_wit_2.
Axiom proof_of_strlen_return_wit_1 : strlen_return_wit_1.

End VC_Correct.
