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
Require Import SimpleC.EE.LLM_bench.Engineering.string.strcat_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
Require Import string_strategy_goal.
Require Import string_strategy_proof.

(*----- Function strcat -----*)

Definition strcat_safety_wit_1 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) ,
  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  (store_string dest_pre dst_str )
  **  (CharArray.undef_seg dest_pre ((string_length (dst_str)) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strcat_safety_wit_2 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) ,
  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (dst_str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (dst_str) (0)) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string dest_pre dst_str )
  **  (CharArray.undef_seg dest_pre ((string_length (dst_str)) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strcat_safety_wit_3 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (dst_str)) 0) <> 0) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (dst_str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (dst_str) (0)) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string dest_pre dst_str )
  **  (CharArray.undef_seg dest_pre ((string_length (dst_str)) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition strcat_safety_wit_4 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (dst_str)) 0) = 0) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (dst_str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (dst_str) (0)) <> 0)) ”
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string dest_pre dst_str )
  **  (CharArray.undef_seg dest_pre ((string_length (dst_str)) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strcat_safety_wit_5 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (j: Z) (i: Z) ,
  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (string_length (src_str))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (CharArray.full dest_pre ((string_length (dst_str)) + j ) (app (dst_str) ((sublist (0) (j) (src_str)))) )
  **  (((dest_pre + (((string_length (dst_str)) + j ) * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strcat_safety_wit_6 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) (j: Z) ,
  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (string_length (src_str))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (CharArray.full dest_pre ((string_length (dst_str)) + j ) (app (dst_str) ((sublist (0) (j) (src_str)))) )
  **  (((dest_pre + (((string_length (dst_str)) + j ) * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ ((i + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + j )) ”
.

Definition strcat_safety_wit_7 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) (j: Z) ,
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ (0 <= ((string_length (dst_str)) + j )) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (string_length (src_str))) ”
  &&  (CharArray.full dest_pre (((string_length (dst_str)) + j ) + 1 ) (app ((app (dst_str) ((sublist (0) (j) (src_str))))) ((cons ((Znth j (c_string (src_str)) 0)) (nil)))) )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition strcat_safety_wit_8 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) (j: Z) ,
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ (0 <= ((string_length (dst_str)) + j )) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (string_length (src_str))) ”
  &&  (CharArray.full dest_pre (((string_length (dst_str)) + j ) + 1 ) (app ((app (dst_str) ((sublist (0) (j) (src_str))))) ((cons ((Znth j (c_string (src_str)) 0)) (nil)))) )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
|--
  “ ((i + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + (j + 1 ) )) ”
.

Definition strcat_safety_wit_9 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) (j: Z) ,
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ (0 <= ((string_length (dst_str)) + j )) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (string_length (src_str))) ”
  &&  (CharArray.full dest_pre (((string_length (dst_str)) + j ) + 1 ) (app ((app (dst_str) ((sublist (0) (j) (src_str))))) ((cons ((Znth j (c_string (src_str)) 0)) (nil)))) )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strcat_entail_wit_1 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) ,
  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ”
  &&  (store_string dest_pre dst_str )
  **  (CharArray.undef_seg dest_pre ((string_length (dst_str)) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (string_length (dst_str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) (dst_str) (0)) <> 0)) ”
  &&  (store_string dest_pre dst_str )
  **  (CharArray.undef_seg dest_pre ((string_length (dst_str)) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
  **  (store_string src_pre src_str )
.

Definition strcat_entail_wit_2 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (dst_str)) 0) <> 0) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (dst_str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (dst_str) (0)) <> 0)) ”
  &&  (store_string dest_pre dst_str )
  **  (CharArray.undef_seg dest_pre ((string_length (dst_str)) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (string_length (dst_str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (dst_str) (0)) <> 0)) ”
  &&  (store_string dest_pre dst_str )
  **  (CharArray.undef_seg dest_pre ((string_length (dst_str)) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
  **  (store_string src_pre src_str )
.

Definition strcat_entail_wit_3 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (dst_str)) 0) = 0) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (dst_str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (dst_str) (0)) <> 0)) ”
  &&  (store_string dest_pre dst_str )
  **  (CharArray.undef_seg dest_pre ((string_length (dst_str)) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre ((string_length (dst_str)) + 0 ) (app (dst_str) ((sublist (0) (0) (src_str)))) )
  **  (((dest_pre + (((string_length (dst_str)) + 0 ) * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + 0 ) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
  **  (store_string src_pre src_str )
.

Definition strcat_entail_wit_4 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth j (c_string (src_str)) 0) <> 0) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre ((string_length (dst_str)) + j ) (app (dst_str) ((sublist (0) (j) (src_str)))) )
  **  (((dest_pre + (((string_length (dst_str)) + j ) * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (string_length (src_str))) ”
  &&  (CharArray.full dest_pre ((string_length (dst_str)) + j ) (app (dst_str) ((sublist (0) (j) (src_str)))) )
  **  (((dest_pre + (((string_length (dst_str)) + j ) * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
  **  (store_string src_pre src_str )
.

Definition strcat_entail_wit_5 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) (j: Z) ,
  “ (0 <= (((string_length (dst_str)) + j ) + 1 )) ” 
  &&  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ (0 <= ((string_length (dst_str)) + j )) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (string_length (src_str))) ”
  &&  (CharArray.full dest_pre ((((string_length (dst_str)) + j ) + 1 ) + 1 ) (app ((app ((app (dst_str) ((sublist (0) (j) (src_str))))) ((cons ((Znth j (c_string (src_str)) 0)) (nil))))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg dest_pre ((i + (j + 1 ) ) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
|--
  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre ((string_length (dst_str)) + (j + 1 ) ) (app (dst_str) ((sublist (0) ((j + 1 )) (src_str)))) )
  **  (((dest_pre + (((string_length (dst_str)) + (j + 1 ) ) * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + (j + 1 ) ) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
  **  (store_string src_pre src_str )
.

Definition strcat_return_wit_1 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth j (c_string (src_str)) 0) = 0) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre ((string_length (dst_str)) + j ) (app (dst_str) ((sublist (0) (j) (src_str)))) )
  **  (((dest_pre + (((string_length (dst_str)) + j ) * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (dest_pre = dest_pre) ”
  &&  (store_string dest_pre (app (dst_str) (src_str)) )
  **  (store_string src_pre src_str )
.

Definition strcat_partial_solve_wit_1 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) (j: Z) ,
  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (string_length (src_str))) ”
  &&  (CharArray.full dest_pre ((string_length (dst_str)) + j ) (app (dst_str) ((sublist (0) (j) (src_str)))) )
  **  (((dest_pre + (((string_length (dst_str)) + j ) * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ (0 <= ((string_length (dst_str)) + j )) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (string_length (src_str))) ”
  &&  (((dest_pre + ((i + j ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  (CharArray.full dest_pre ((string_length (dst_str)) + j ) (app (dst_str) ((sublist (0) (j) (src_str)))) )
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
.

Definition strcat_partial_solve_wit_2 := 
forall (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) (j: Z) ,
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ (0 <= ((string_length (dst_str)) + j )) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (string_length (src_str))) ”
  &&  (CharArray.full dest_pre (((string_length (dst_str)) + j ) + 1 ) (app ((app (dst_str) ((sublist (0) (j) (src_str))))) ((cons ((Znth j (c_string (src_str)) 0)) (nil)))) )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
|--
  “ (0 <= (((string_length (dst_str)) + j ) + 1 )) ” 
  &&  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ (0 <= ((string_length (dst_str)) + j )) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ ((((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (string_length (src_str))) ”
  &&  (((dest_pre + ((i + (j + 1 ) ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i dest_pre (i + (j + 1 ) ) (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + (string_length (src_str)) ) + 1 ) )
  **  (CharArray.full dest_pre (((string_length (dst_str)) + j ) + 1 ) (app ((app (dst_str) ((sublist (0) (j) (src_str))))) ((cons ((Znth j (c_string (src_str)) 0)) (nil)))) )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
.

(*----- Function strncat -----*)

Definition strncat_safety_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) ,
  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  (store_string dest_pre dst_str )
  **  (CharArray.undef_seg dest_pre ((string_length (dst_str)) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strncat_safety_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) ,
  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (dst_str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (dst_str) (0)) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string dest_pre dst_str )
  **  (CharArray.undef_seg dest_pre ((string_length (dst_str)) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strncat_safety_wit_3 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (dst_str)) 0) <> 0) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (dst_str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (dst_str) (0)) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string dest_pre dst_str )
  **  (CharArray.undef_seg dest_pre ((string_length (dst_str)) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition strncat_safety_wit_4 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (dst_str)) 0) = 0) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (dst_str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (dst_str) (0)) <> 0)) ”
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string dest_pre dst_str )
  **  (CharArray.undef_seg dest_pre ((string_length (dst_str)) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strncat_safety_wit_5 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (j: Z) (i: Z) ,
  “ (j < n_pre) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (j <= (string_length (src_str))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full dest_pre ((string_length (dst_str)) + j ) (app (dst_str) ((sublist (0) (j) (src_str)))) )
  **  (((dest_pre + (((string_length (dst_str)) + j ) * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strncat_safety_wit_6 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) (j: Z) ,
  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (j < (string_length (src_str))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full dest_pre ((string_length (dst_str)) + j ) (app (dst_str) ((sublist (0) (j) (src_str)))) )
  **  (((dest_pre + (((string_length (dst_str)) + j ) * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ ((i + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + j )) ”
.

Definition strncat_safety_wit_7 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) (j: Z) ,
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ (0 <= ((string_length (dst_str)) + j )) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (j < (string_length (src_str))) ”
  &&  (CharArray.full dest_pre (((string_length (dst_str)) + j ) + 1 ) (app ((app (dst_str) ((sublist (0) (j) (src_str))))) ((cons ((Znth j (c_string (src_str)) 0)) (nil)))) )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition strncat_safety_wit_8 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) (j: Z) ,
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ (0 <= ((string_length (dst_str)) + j )) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (j < (string_length (src_str))) ”
  &&  (CharArray.full dest_pre (((string_length (dst_str)) + j ) + 1 ) (app ((app (dst_str) ((sublist (0) (j) (src_str))))) ((cons ((Znth j (c_string (src_str)) 0)) (nil)))) )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
|--
  “ ((i + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + (j + 1 ) )) ”
.

Definition strncat_safety_wit_9 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) (j: Z) ,
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ (0 <= ((string_length (dst_str)) + j )) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (j < (string_length (src_str))) ”
  &&  (CharArray.full dest_pre (((string_length (dst_str)) + j ) + 1 ) (app ((app (dst_str) ((sublist (0) (j) (src_str))))) ((cons ((Znth j (c_string (src_str)) 0)) (nil)))) )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strncat_entail_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) ,
  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ”
  &&  (store_string dest_pre dst_str )
  **  (CharArray.undef_seg dest_pre ((string_length (dst_str)) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (string_length (dst_str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) (dst_str) (0)) <> 0)) ”
  &&  (store_string dest_pre dst_str )
  **  (CharArray.undef_seg dest_pre ((string_length (dst_str)) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
  **  (store_string src_pre src_str )
.

Definition strncat_entail_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (dst_str)) 0) <> 0) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (dst_str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (dst_str) (0)) <> 0)) ”
  &&  (store_string dest_pre dst_str )
  **  (CharArray.undef_seg dest_pre ((string_length (dst_str)) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (string_length (dst_str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (dst_str) (0)) <> 0)) ”
  &&  (store_string dest_pre dst_str )
  **  (CharArray.undef_seg dest_pre ((string_length (dst_str)) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
  **  (store_string src_pre src_str )
.

Definition strncat_entail_wit_3 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) ,
  “ ((Znth i (c_string (dst_str)) 0) = 0) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (dst_str))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (dst_str) (0)) <> 0)) ”
  &&  (store_string dest_pre dst_str )
  **  (CharArray.undef_seg dest_pre ((string_length (dst_str)) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre ((string_length (dst_str)) + 0 ) (app (dst_str) ((sublist (0) (0) (src_str)))) )
  **  (((dest_pre + (((string_length (dst_str)) + 0 ) * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + 0 ) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
  **  (store_string src_pre src_str )
.

Definition strncat_entail_wit_4 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth j (c_string (src_str)) 0) <> 0) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (j <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre ((string_length (dst_str)) + j ) (app (dst_str) ((sublist (0) (j) (src_str)))) )
  **  (((dest_pre + (((string_length (dst_str)) + j ) * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (j < (string_length (src_str))) ”
  &&  (CharArray.full dest_pre ((string_length (dst_str)) + j ) (app (dst_str) ((sublist (0) (j) (src_str)))) )
  **  (((dest_pre + (((string_length (dst_str)) + j ) * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
  **  (store_string src_pre src_str )
.

Definition strncat_entail_wit_5 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) (j: Z) ,
  “ (0 <= (((string_length (dst_str)) + j ) + 1 )) ” 
  &&  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ (0 <= ((string_length (dst_str)) + j )) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (j < (string_length (src_str))) ”
  &&  (CharArray.full dest_pre ((((string_length (dst_str)) + j ) + 1 ) + 1 ) (app ((app ((app (dst_str) ((sublist (0) (j) (src_str))))) ((cons ((Znth j (c_string (src_str)) 0)) (nil))))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg dest_pre ((i + (j + 1 ) ) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
|--
  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ ((j + 1 ) <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre ((string_length (dst_str)) + (j + 1 ) ) (app (dst_str) ((sublist (0) ((j + 1 )) (src_str)))) )
  **  (((dest_pre + (((string_length (dst_str)) + (j + 1 ) ) * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + (j + 1 ) ) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
  **  (store_string src_pre src_str )
.

Definition strncat_return_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (j: Z) (i: Z) ,
  “ (j >= n_pre) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (j <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre ((string_length (dst_str)) + j ) (app (dst_str) ((sublist (0) (j) (src_str)))) )
  **  (((dest_pre + (((string_length (dst_str)) + j ) * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  EX (out: (@list Z)) ,
  “ (strncat_result dst_str src_str n_pre out ) ” 
  &&  “ (dest_pre = dest_pre) ”
  &&  (store_string dest_pre out )
  **  (CharArray.undef_seg dest_pre ((string_length (out)) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
  **  (store_string src_pre src_str )
.

Definition strncat_return_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth j (c_string (src_str)) 0) = 0) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (j <= (string_length (src_str))) ”
  &&  (CharArray.full dest_pre ((string_length (dst_str)) + j ) (app (dst_str) ((sublist (0) (j) (src_str)))) )
  **  (((dest_pre + (((string_length (dst_str)) + j ) * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  EX (out: (@list Z)) ,
  “ (strncat_result dst_str src_str n_pre out ) ” 
  &&  “ (dest_pre = dest_pre) ”
  &&  (store_string dest_pre out )
  **  (CharArray.undef_seg dest_pre ((string_length (out)) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
  **  (store_string src_pre src_str )
.

Definition strncat_partial_solve_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) (j: Z) ,
  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (j < (string_length (src_str))) ”
  &&  (CharArray.full dest_pre ((string_length (dst_str)) + j ) (app (dst_str) ((sublist (0) (j) (src_str)))) )
  **  (((dest_pre + (((string_length (dst_str)) + j ) * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
  **  (store_string src_pre src_str )
|--
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ (0 <= ((string_length (dst_str)) + j )) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (j < (string_length (src_str))) ”
  &&  (((dest_pre + ((i + j ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  (CharArray.full dest_pre ((string_length (dst_str)) + j ) (app (dst_str) ((sublist (0) (j) (src_str)))) )
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
.

Definition strncat_partial_solve_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (src_str: (@list Z)) (dst_str: (@list Z)) (i: Z) (j: Z) ,
  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ (0 <= ((string_length (dst_str)) + j )) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (j < (string_length (src_str))) ”
  &&  (CharArray.full dest_pre (((string_length (dst_str)) + j ) + 1 ) (app ((app (dst_str) ((sublist (0) (j) (src_str))))) ((cons ((Znth j (c_string (src_str)) 0)) (nil)))) )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
  **  (CharArray.undef_seg dest_pre (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
|--
  “ (0 <= (((string_length (dst_str)) + j ) + 1 )) ” 
  &&  “ (0 <= ((string_length (src_str)) + 1 )) ” 
  &&  “ (0 <= ((string_length (dst_str)) + j )) ” 
  &&  “ (valid_string dst_str ) ” 
  &&  “ (valid_string src_str ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((((string_length (dst_str)) + n_pre ) + 1 ) < INT_MAX) ” 
  &&  “ (i = (string_length (dst_str))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (j < (string_length (src_str))) ”
  &&  (((dest_pre + ((i + (j + 1 ) ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i dest_pre (i + (j + 1 ) ) (((string_length (dst_str)) + j ) + 1 ) (((string_length (dst_str)) + n_pre ) + 1 ) )
  **  (CharArray.full dest_pre (((string_length (dst_str)) + j ) + 1 ) (app ((app (dst_str) ((sublist (0) (j) (src_str))))) ((cons ((Znth j (c_string (src_str)) 0)) (nil)))) )
  **  (CharArray.full src_pre ((string_length (src_str)) + 1 ) (c_string (src_str)) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_strcat_safety_wit_1 : strcat_safety_wit_1.
Axiom proof_of_strcat_safety_wit_2 : strcat_safety_wit_2.
Axiom proof_of_strcat_safety_wit_3 : strcat_safety_wit_3.
Axiom proof_of_strcat_safety_wit_4 : strcat_safety_wit_4.
Axiom proof_of_strcat_safety_wit_5 : strcat_safety_wit_5.
Axiom proof_of_strcat_safety_wit_6 : strcat_safety_wit_6.
Axiom proof_of_strcat_safety_wit_7 : strcat_safety_wit_7.
Axiom proof_of_strcat_safety_wit_8 : strcat_safety_wit_8.
Axiom proof_of_strcat_safety_wit_9 : strcat_safety_wit_9.
Axiom proof_of_strcat_entail_wit_1 : strcat_entail_wit_1.
Axiom proof_of_strcat_entail_wit_2 : strcat_entail_wit_2.
Axiom proof_of_strcat_entail_wit_3 : strcat_entail_wit_3.
Axiom proof_of_strcat_entail_wit_4 : strcat_entail_wit_4.
Axiom proof_of_strcat_entail_wit_5 : strcat_entail_wit_5.
Axiom proof_of_strcat_return_wit_1 : strcat_return_wit_1.
Axiom proof_of_strcat_partial_solve_wit_1 : strcat_partial_solve_wit_1.
Axiom proof_of_strcat_partial_solve_wit_2 : strcat_partial_solve_wit_2.
Axiom proof_of_strncat_safety_wit_1 : strncat_safety_wit_1.
Axiom proof_of_strncat_safety_wit_2 : strncat_safety_wit_2.
Axiom proof_of_strncat_safety_wit_3 : strncat_safety_wit_3.
Axiom proof_of_strncat_safety_wit_4 : strncat_safety_wit_4.
Axiom proof_of_strncat_safety_wit_5 : strncat_safety_wit_5.
Axiom proof_of_strncat_safety_wit_6 : strncat_safety_wit_6.
Axiom proof_of_strncat_safety_wit_7 : strncat_safety_wit_7.
Axiom proof_of_strncat_safety_wit_8 : strncat_safety_wit_8.
Axiom proof_of_strncat_safety_wit_9 : strncat_safety_wit_9.
Axiom proof_of_strncat_entail_wit_1 : strncat_entail_wit_1.
Axiom proof_of_strncat_entail_wit_2 : strncat_entail_wit_2.
Axiom proof_of_strncat_entail_wit_3 : strncat_entail_wit_3.
Axiom proof_of_strncat_entail_wit_4 : strncat_entail_wit_4.
Axiom proof_of_strncat_entail_wit_5 : strncat_entail_wit_5.
Axiom proof_of_strncat_return_wit_1 : strncat_return_wit_1.
Axiom proof_of_strncat_return_wit_2 : strncat_return_wit_2.
Axiom proof_of_strncat_partial_solve_wit_1 : strncat_partial_solve_wit_1.
Axiom proof_of_strncat_partial_solve_wit_2 : strncat_partial_solve_wit_2.

End VC_Correct.
