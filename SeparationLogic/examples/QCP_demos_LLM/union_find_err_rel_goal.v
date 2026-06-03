Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
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
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.kmp_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Require Import SimpleC.EE.QCP_demos_LLM.union_find_err_rel_lib.
Local Open Scope monad.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_proof.

(*----- Function uf_find_c -----*)

Definition uf_find_c_entail_wit_1 := 
forall (x_pre: Z) (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (Z -> (uf_state -> Prop))) (rs_low_level_spec: (@list Z)) (ps_low_level_spec: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps_low_level_spec) (rs_low_level_spec)))) (uf_find (x_pre)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps_low_level_spec )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ ((Znth x_pre ps_low_level_spec 0) = (Znth (x_pre) (ps_low_level_spec) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps_low_level_spec) (rs_low_level_spec)))) (uf_find_after_read (x_pre) ((Znth x_pre ps_low_level_spec 0))) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps_low_level_spec )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
.

Definition uf_find_c_entail_wit_2 := 
forall (x_pre: Z) (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (Z -> (uf_state -> Prop))) (rs_low_level_spec: (@list Z)) (ps_low_level_spec: (@list Z)) (p: Z) ,
  “ (p <> x_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (p = (Znth (x_pre) (ps_low_level_spec) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps_low_level_spec) (rs_low_level_spec)))) (uf_find_after_read (x_pre) (p)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps_low_level_spec )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < n_pre) ” 
  &&  “ (p = (Znth (x_pre) (ps_low_level_spec) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps_low_level_spec) (rs_low_level_spec)))) (bind ((uf_find (p))) ((uf_find_after_rec (x_pre)))) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps_low_level_spec )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
.

Definition uf_find_c_entail_wit_3 := 
forall (x_pre: Z) (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (Z -> (uf_state -> Prop))) (rs_low_level_spec: (@list Z)) (ps_low_level_spec: (@list Z)) (p: Z) (ps1_2: (@list Z)) (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps1_2) (rs_low_level_spec)))) (applyf ((uf_find_after_rec (x_pre))) (retval)) X_low_level_spec ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < n_pre) ” 
  &&  “ (p = (Znth (x_pre) (ps_low_level_spec) (0))) ”
  &&  (IntArray.full parent_pre n_pre ps1_2 )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
|--
  EX (ps1: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < n_pre) ” 
  &&  “ (p = (Znth (x_pre) (ps_low_level_spec) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps1) (rs_low_level_spec)))) (applyf ((uf_find_after_rec (x_pre))) (retval)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps1 )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
.

Definition uf_find_c_entail_wit_4 := 
forall (x_pre: Z) (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (Z -> (uf_state -> Prop))) (rs_low_level_spec: (@list Z)) (ps_low_level_spec: (@list Z)) (ps1_2: (@list Z)) (r: Z) (p: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < n_pre) ” 
  &&  “ (p = (Znth (x_pre) (ps_low_level_spec) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps1_2) (rs_low_level_spec)))) (applyf ((uf_find_after_rec (x_pre))) (r)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre (replace_Znth (x_pre) (r) (ps1_2)) )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
|--
  EX (ps1: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (p = (Znth (x_pre) (ps_low_level_spec) (0))) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) ((replace_Znth (x_pre) (r) (ps1))) (rs_low_level_spec)))) (return (r)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre (replace_Znth (x_pre) (r) (ps1)) )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
.

Definition uf_find_c_return_wit_1 := 
forall (x_pre: Z) (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (Z -> (uf_state -> Prop))) (rs_low_level_spec: (@list Z)) (ps_low_level_spec: (@list Z)) (ps1_2: (@list Z)) (p: Z) (r: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (p = (Znth (x_pre) (ps_low_level_spec) (0))) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) ((replace_Znth (x_pre) (r) (ps1_2))) (rs_low_level_spec)))) (return (r)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre (replace_Znth (x_pre) (r) (ps1_2)) )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
|--
  EX (ps1: (@list Z)) ,
  “ (0 <= r) ” 
  &&  “ (r < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps1) (rs_low_level_spec)))) (return (r)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps1 )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
.

Definition uf_find_c_return_wit_2 := 
forall (x_pre: Z) (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (Z -> (uf_state -> Prop))) (rs_low_level_spec: (@list Z)) (ps_low_level_spec: (@list Z)) (p: Z) ,
  “ (p = x_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (p = (Znth (x_pre) (ps_low_level_spec) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps_low_level_spec) (rs_low_level_spec)))) (uf_find_after_read (x_pre) (p)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps_low_level_spec )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
|--
  EX (ps1: (@list Z)) ,
  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps1) (rs_low_level_spec)))) (return (x_pre)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps1 )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
.

Definition uf_find_c_partial_solve_wit_1 := 
forall (x_pre: Z) (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (Z -> (uf_state -> Prop))) (rs_low_level_spec: (@list Z)) (ps_low_level_spec: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps_low_level_spec) (rs_low_level_spec)))) (uf_find (x_pre)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps_low_level_spec )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps_low_level_spec) (rs_low_level_spec)))) (uf_find (x_pre)) X_low_level_spec ) ”
  &&  (((parent_pre + (x_pre * sizeof(INT) ) )) # Int  |-> (Znth x_pre ps_low_level_spec 0))
  **  (IntArray.missing_i parent_pre x_pre 0 n_pre ps_low_level_spec )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
.

Definition uf_find_c_partial_solve_wit_2_pure := 
forall (x_pre: Z) (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (Z -> (uf_state -> Prop))) (rs_low_level_spec: (@list Z)) (ps_low_level_spec: (@list Z)) (p: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < n_pre) ” 
  &&  “ (p = (Znth (x_pre) (ps_low_level_spec) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps_low_level_spec) (rs_low_level_spec)))) (bind ((uf_find (p))) ((uf_find_after_rec (x_pre)))) X_low_level_spec ) ”
  &&  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "rank" ) )) # Ptr  |-> rank_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  (IntArray.full parent_pre n_pre ps_low_level_spec )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps_low_level_spec) (rs_low_level_spec)))) (bind ((uf_find (p))) ((uf_find_after_rec (x_pre)))) X_low_level_spec ) ” 
  &&  “ (equiv (uf_find_after_rec (x_pre)) (uf_find_after_rec (x_pre)) ) ”
.

Definition uf_find_c_partial_solve_wit_2_aux := 
forall (x_pre: Z) (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (Z -> (uf_state -> Prop))) (rs_low_level_spec: (@list Z)) (ps_low_level_spec: (@list Z)) (p: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < n_pre) ” 
  &&  “ (p = (Znth (x_pre) (ps_low_level_spec) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps_low_level_spec) (rs_low_level_spec)))) (bind ((uf_find (p))) ((uf_find_after_rec (x_pre)))) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps_low_level_spec )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps_low_level_spec) (rs_low_level_spec)))) (bind ((uf_find (p))) ((uf_find_after_rec (x_pre)))) X_low_level_spec ) ” 
  &&  “ (equiv (uf_find_after_rec (x_pre)) (uf_find_after_rec (x_pre)) ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < n_pre) ” 
  &&  “ (p = (Znth (x_pre) (ps_low_level_spec) (0))) ”
  &&  (IntArray.full parent_pre n_pre ps_low_level_spec )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
.

Definition uf_find_c_partial_solve_wit_2 := uf_find_c_partial_solve_wit_2_pure -> uf_find_c_partial_solve_wit_2_aux.

Definition uf_find_c_partial_solve_wit_3 := 
forall (x_pre: Z) (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (Z -> (uf_state -> Prop))) (rs_low_level_spec: (@list Z)) (ps_low_level_spec: (@list Z)) (ps1: (@list Z)) (r: Z) (p: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < n_pre) ” 
  &&  “ (p = (Znth (x_pre) (ps_low_level_spec) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps1) (rs_low_level_spec)))) (applyf ((uf_find_after_rec (x_pre))) (r)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps1 )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < n_pre) ” 
  &&  “ (p = (Znth (x_pre) (ps_low_level_spec) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps1) (rs_low_level_spec)))) (applyf ((uf_find_after_rec (x_pre))) (r)) X_low_level_spec ) ”
  &&  (((parent_pre + (x_pre * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i parent_pre x_pre 0 n_pre ps1 )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
.

(*----- Function uf_union_c -----*)

Definition uf_union_c_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (ps2: (@list Z)) (rs2: (@list Z)) (rx: Z) (ry: Z) (rx_rank: Z) (ry_rank: Z) ,
  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (rx_rank = ry_rank) ” 
  &&  “ (ry_rank = (Znth (ry) (rs2) (0))) ” 
  &&  “ ((ry_rank + 1 ) <= INT_MAX) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) ((replace_Znth (rx) (ry) (ps2))) (rs2)))) (bump_rank (ry)) X_low_level_spec ) ”
  &&  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "rank" ) )) # Ptr  |-> rank_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "rx" ) )) # Int  |-> rx)
  **  ((( &( "ry" ) )) # Int  |-> ry)
  **  ((( &( "rx_rank" ) )) # Int  |-> rx_rank)
  **  ((( &( "ry_rank" ) )) # Int  |-> ry_rank)
  **  (IntArray.full parent_pre n_pre (replace_Znth (rx) (ry) (ps2)) )
  **  (IntArray.full rank_pre n_pre rs2 )
|--
  “ ((ry_rank + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ry_rank + 1 )) ”
.

Definition uf_union_c_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (ps2: (@list Z)) (rs2: (@list Z)) (rx: Z) (ry: Z) (rx_rank: Z) (ry_rank: Z) ,
  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (rx_rank = ry_rank) ” 
  &&  “ (ry_rank = (Znth (ry) (rs2) (0))) ” 
  &&  “ ((ry_rank + 1 ) <= INT_MAX) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) ((replace_Znth (rx) (ry) (ps2))) (rs2)))) (bump_rank (ry)) X_low_level_spec ) ”
  &&  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "rank" ) )) # Ptr  |-> rank_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "rx" ) )) # Int  |-> rx)
  **  ((( &( "ry" ) )) # Int  |-> ry)
  **  ((( &( "rx_rank" ) )) # Int  |-> rx_rank)
  **  ((( &( "ry_rank" ) )) # Int  |-> ry_rank)
  **  (IntArray.full parent_pre n_pre (replace_Znth (rx) (ry) (ps2)) )
  **  (IntArray.full rank_pre n_pre rs2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition uf_union_c_entail_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (rs_low_level_spec: (@list Z)) (ps_low_level_spec: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (0 <= y_pre) ” 
  &&  “ (y_pre < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps_low_level_spec) (rs_low_level_spec)))) (uf_union (x_pre) (y_pre)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps_low_level_spec )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (0 <= y_pre) ” 
  &&  “ (y_pre < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps_low_level_spec) (rs_low_level_spec)))) (bind ((uf_find (x_pre))) ((uf_union_after_find_x (y_pre)))) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps_low_level_spec )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
.

Definition uf_union_c_entail_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (rs_low_level_spec: (@list Z)) (ps1_2: (@list Z)) (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps1_2) (rs_low_level_spec)))) (applyf ((uf_union_after_find_x (y_pre))) (retval)) X_low_level_spec ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (0 <= y_pre) ” 
  &&  “ (y_pre < n_pre) ”
  &&  (IntArray.full parent_pre n_pre ps1_2 )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
|--
  EX (ps1: (@list Z))  (rs1: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < n_pre) ” 
  &&  “ (0 <= y_pre) ” 
  &&  “ (y_pre < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps1) (rs1)))) (applyf ((uf_union_after_find_x (y_pre))) (retval)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps1 )
  **  (IntArray.full rank_pre n_pre rs1 )
.

Definition uf_union_c_entail_wit_3 := 
forall (y_pre: Z) (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (rs1: (@list Z)) (rx: Z) (ps1: (@list Z)) (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps1) (rs1)))) (applyf ((uf_union_after_find_y (rx))) (retval)) X_low_level_spec ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= y_pre) ” 
  &&  “ (y_pre < n_pre) ”
  &&  (IntArray.full parent_pre n_pre ps1 )
  **  (IntArray.full rank_pre n_pre rs1 )
|--
  EX (ps2: (@list Z))  (rs2: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps2) (rs2)))) (applyf ((uf_union_after_find_y (rx))) (retval)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps2 )
  **  (IntArray.full rank_pre n_pre rs2 )
.

Definition uf_union_c_entail_wit_4 := 
forall (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (ps2_2: (@list Z)) (rs2_2: (@list Z)) (rx: Z) (ry: Z) ,
  “ (rx = ry) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps2_2) (rs2_2)))) (applyf ((uf_union_after_find_y (rx))) (ry)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps2_2 )
  **  (IntArray.full rank_pre n_pre rs2_2 )
|--
  EX (ps2: (@list Z))  (rs2: (@list Z)) ,
  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (ry = rx) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps2) (rs2)))) (return (tt)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps2 )
  **  (IntArray.full rank_pre n_pre rs2 )
.

Definition uf_union_c_entail_wit_5 := 
forall (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (ps2_2: (@list Z)) (rs2: (@list Z)) (rx: Z) (ry: Z) ,
  “ (rx <> ry) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps2_2) (rs2)))) (applyf ((uf_union_after_find_y (rx))) (ry)) X_low_level_spec ) ”
  &&  (IntArray.full rank_pre n_pre rs2 )
  **  (IntArray.full parent_pre n_pre ps2_2 )
|--
  EX (ps2: (@list Z))  (rs2_2: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ ((Znth rx rs2 0) = (Znth (rx) (rs2_2) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps2) (rs2_2)))) (uf_union_after_rank_rx (rx) (ry) ((Znth rx rs2 0))) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps2 )
  **  (IntArray.full rank_pre n_pre rs2_2 )
.

Definition uf_union_c_entail_wit_6 := 
forall (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (ps2_2: (@list Z)) (rs2: (@list Z)) (rx: Z) (ry: Z) (rx_rank: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (rx_rank = (Znth (rx) (rs2) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps2_2) (rs2)))) (uf_union_after_rank_rx (rx) (ry) (rx_rank)) X_low_level_spec ) ”
  &&  (IntArray.full rank_pre n_pre rs2 )
  **  (IntArray.full parent_pre n_pre ps2_2 )
|--
  EX (ps2: (@list Z))  (rs2_2: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (rx_rank = (Znth (rx) (rs2_2) (0))) ” 
  &&  “ ((Znth ry rs2 0) = (Znth (ry) (rs2_2) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps2) (rs2_2)))) (uf_union_after_rank_ry (rx) (ry) (rx_rank) ((Znth ry rs2 0))) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps2 )
  **  (IntArray.full rank_pre n_pre rs2_2 )
.

Definition uf_union_c_entail_wit_7 := 
forall (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (ps2_2: (@list Z)) (rs2_2: (@list Z)) (rx: Z) (ry: Z) (rx_rank: Z) (ry_rank: Z) ,
  “ (ry_rank < rx_rank) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (rx_rank = (Znth (rx) (rs2_2) (0))) ” 
  &&  “ (ry_rank = (Znth (ry) (rs2_2) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps2_2) (rs2_2)))) (uf_union_after_rank_ry (rx) (ry) (rx_rank) (ry_rank)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre (replace_Znth (ry) (rx) (ps2_2)) )
  **  (IntArray.full rank_pre n_pre rs2_2 )
|--
  EX (ps2: (@list Z))  (rs2: (@list Z)) ,
  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (ry_rank < rx_rank) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) ((replace_Znth (ry) (rx) (ps2))) (rs2)))) (return (tt)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre (replace_Znth (ry) (rx) (ps2)) )
  **  (IntArray.full rank_pre n_pre rs2 )
.

Definition uf_union_c_entail_wit_8 := 
forall (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (ps2_2: (@list Z)) (rs2_2: (@list Z)) (rx: Z) (ry: Z) (rx_rank: Z) (ry_rank: Z) ,
  “ (rx_rank < ry_rank) ” 
  &&  “ (ry_rank >= rx_rank) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (rx_rank = (Znth (rx) (rs2_2) (0))) ” 
  &&  “ (ry_rank = (Znth (ry) (rs2_2) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps2_2) (rs2_2)))) (uf_union_after_rank_ry (rx) (ry) (rx_rank) (ry_rank)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre (replace_Znth (rx) (ry) (ps2_2)) )
  **  (IntArray.full rank_pre n_pre rs2_2 )
|--
  EX (ps2: (@list Z))  (rs2: (@list Z)) ,
  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (rx_rank < ry_rank) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) ((replace_Znth (rx) (ry) (ps2))) (rs2)))) (return (tt)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre (replace_Znth (rx) (ry) (ps2)) )
  **  (IntArray.full rank_pre n_pre rs2 )
.

Definition uf_union_c_entail_wit_9 := 
forall (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (ps2_2: (@list Z)) (rs2_2: (@list Z)) (rx: Z) (ry: Z) (rx_rank: Z) (ry_rank: Z) ,
  “ (rx_rank >= ry_rank) ” 
  &&  “ (ry_rank >= rx_rank) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (rx_rank = (Znth (rx) (rs2_2) (0))) ” 
  &&  “ (ry_rank = (Znth (ry) (rs2_2) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps2_2) (rs2_2)))) (uf_union_after_rank_ry (rx) (ry) (rx_rank) (ry_rank)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre (replace_Znth (rx) (ry) (ps2_2)) )
  **  (IntArray.full rank_pre n_pre rs2_2 )
|--
  EX (ps2: (@list Z))  (rs2: (@list Z)) ,
  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (rx_rank = ry_rank) ” 
  &&  “ (ry_rank = (Znth (ry) (rs2) (0))) ” 
  &&  “ ((ry_rank + 1 ) <= INT_MAX) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) ((replace_Znth (rx) (ry) (ps2))) (rs2)))) (bump_rank (ry)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre (replace_Znth (rx) (ry) (ps2)) )
  **  (IntArray.full rank_pre n_pre rs2 )
.

Definition uf_union_c_entail_wit_10 := 
forall (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (ps2_2: (@list Z)) (rs2_2: (@list Z)) (rx: Z) (ry: Z) (rx_rank: Z) (ry_rank: Z) ,
  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (rx_rank = ry_rank) ” 
  &&  “ (ry_rank = (Znth (ry) (rs2_2) (0))) ” 
  &&  “ ((ry_rank + 1 ) <= INT_MAX) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) ((replace_Znth (rx) (ry) (ps2_2))) (rs2_2)))) (bump_rank (ry)) X_low_level_spec ) ”
  &&  (IntArray.full rank_pre n_pre (replace_Znth (ry) ((ry_rank + 1 )) (rs2_2)) )
  **  (IntArray.full parent_pre n_pre (replace_Znth (rx) (ry) (ps2_2)) )
|--
  EX (ps2: (@list Z))  (rs2: (@list Z)) ,
  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (rx_rank = ry_rank) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) ((replace_Znth (rx) (ry) (ps2))) ((replace_Znth (ry) ((ry_rank + 1 )) (rs2)))))) (return (tt)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre (replace_Znth (rx) (ry) (ps2)) )
  **  (IntArray.full rank_pre n_pre (replace_Znth (ry) ((ry_rank + 1 )) (rs2)) )
.

Definition uf_union_c_return_wit_1 := 
forall (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (ps2: (@list Z)) (rs2: (@list Z)) (rx: Z) (ry: Z) ,
  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (ry = rx) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps2) (rs2)))) (return (tt)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps2 )
  **  (IntArray.full rank_pre n_pre rs2 )
|--
  EX (ps1: (@list Z))  (rs1: (@list Z)) ,
  “ (safeExec (equiv ((uf_state_of (n_pre) (ps1) (rs1)))) (return (tt)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps1 )
  **  (IntArray.full rank_pre n_pre rs1 )
.

Definition uf_union_c_return_wit_2 := 
forall (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (ps2: (@list Z)) (rs2: (@list Z)) (rx: Z) (ry: Z) (ry_rank: Z) (rx_rank: Z) ,
  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (ry_rank < rx_rank) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) ((replace_Znth (ry) (rx) (ps2))) (rs2)))) (return (tt)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre (replace_Znth (ry) (rx) (ps2)) )
  **  (IntArray.full rank_pre n_pre rs2 )
|--
  EX (ps1: (@list Z))  (rs1: (@list Z)) ,
  “ (safeExec (equiv ((uf_state_of (n_pre) (ps1) (rs1)))) (return (tt)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps1 )
  **  (IntArray.full rank_pre n_pre rs1 )
.

Definition uf_union_c_return_wit_3 := 
forall (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (ps2: (@list Z)) (rs2: (@list Z)) (rx: Z) (ry: Z) (rx_rank: Z) (ry_rank: Z) ,
  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (rx_rank < ry_rank) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) ((replace_Znth (rx) (ry) (ps2))) (rs2)))) (return (tt)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre (replace_Znth (rx) (ry) (ps2)) )
  **  (IntArray.full rank_pre n_pre rs2 )
|--
  EX (ps1: (@list Z))  (rs1: (@list Z)) ,
  “ (safeExec (equiv ((uf_state_of (n_pre) (ps1) (rs1)))) (return (tt)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps1 )
  **  (IntArray.full rank_pre n_pre rs1 )
.

Definition uf_union_c_return_wit_4 := 
forall (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (ps2: (@list Z)) (rs2: (@list Z)) (rx: Z) (ry: Z) (rx_rank: Z) (ry_rank: Z) ,
  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (rx_rank = ry_rank) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) ((replace_Znth (rx) (ry) (ps2))) ((replace_Znth (ry) ((ry_rank + 1 )) (rs2)))))) (return (tt)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre (replace_Znth (rx) (ry) (ps2)) )
  **  (IntArray.full rank_pre n_pre (replace_Znth (ry) ((ry_rank + 1 )) (rs2)) )
|--
  EX (ps1: (@list Z))  (rs1: (@list Z)) ,
  “ (safeExec (equiv ((uf_state_of (n_pre) (ps1) (rs1)))) (return (tt)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps1 )
  **  (IntArray.full rank_pre n_pre rs1 )
.

Definition uf_union_c_partial_solve_wit_1_pure := 
forall (y_pre: Z) (x_pre: Z) (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (rs_low_level_spec: (@list Z)) (ps_low_level_spec: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (0 <= y_pre) ” 
  &&  “ (y_pre < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps_low_level_spec) (rs_low_level_spec)))) (bind ((uf_find (x_pre))) ((uf_union_after_find_x (y_pre)))) X_low_level_spec ) ”
  &&  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "rank" ) )) # Ptr  |-> rank_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "rx" ) )) # Int  |->_)
  **  (IntArray.full parent_pre n_pre ps_low_level_spec )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps_low_level_spec) (rs_low_level_spec)))) (bind ((uf_find (x_pre))) ((uf_union_after_find_x (y_pre)))) X_low_level_spec ) ” 
  &&  “ (equiv (uf_union_after_find_x (y_pre)) (uf_union_after_find_x (y_pre)) ) ”
.

Definition uf_union_c_partial_solve_wit_1_aux := 
forall (y_pre: Z) (x_pre: Z) (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (rs_low_level_spec: (@list Z)) (ps_low_level_spec: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (0 <= y_pre) ” 
  &&  “ (y_pre < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps_low_level_spec) (rs_low_level_spec)))) (bind ((uf_find (x_pre))) ((uf_union_after_find_x (y_pre)))) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps_low_level_spec )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps_low_level_spec) (rs_low_level_spec)))) (bind ((uf_find (x_pre))) ((uf_union_after_find_x (y_pre)))) X_low_level_spec ) ” 
  &&  “ (equiv (uf_union_after_find_x (y_pre)) (uf_union_after_find_x (y_pre)) ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (0 <= y_pre) ” 
  &&  “ (y_pre < n_pre) ”
  &&  (IntArray.full parent_pre n_pre ps_low_level_spec )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec )
.

Definition uf_union_c_partial_solve_wit_1 := uf_union_c_partial_solve_wit_1_pure -> uf_union_c_partial_solve_wit_1_aux.

Definition uf_union_c_partial_solve_wit_2_pure := 
forall (y_pre: Z) (x_pre: Z) (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (ps1: (@list Z)) (rs1: (@list Z)) (rx: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= y_pre) ” 
  &&  “ (y_pre < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps1) (rs1)))) (applyf ((uf_union_after_find_x (y_pre))) (rx)) X_low_level_spec ) ”
  &&  ((( &( "ry" ) )) # Int  |->_)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "rank" ) )) # Ptr  |-> rank_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "rx" ) )) # Int  |-> rx)
  **  (IntArray.full parent_pre n_pre ps1 )
  **  (IntArray.full rank_pre n_pre rs1 )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= y_pre) ” 
  &&  “ (y_pre < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps1) (rs1)))) (bind ((uf_find (y_pre))) ((uf_union_after_find_y (rx)))) X_low_level_spec ) ” 
  &&  “ (equiv (applyf ((uf_union_after_find_x (y_pre))) (rx)) (bind ((uf_find (y_pre))) ((uf_union_after_find_y (rx)))) ) ”
.

Definition uf_union_c_partial_solve_wit_2_aux := 
forall (y_pre: Z) (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (ps1: (@list Z)) (rs1: (@list Z)) (rx: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= y_pre) ” 
  &&  “ (y_pre < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps1) (rs1)))) (applyf ((uf_union_after_find_x (y_pre))) (rx)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps1 )
  **  (IntArray.full rank_pre n_pre rs1 )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= y_pre) ” 
  &&  “ (y_pre < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps1) (rs1)))) (bind ((uf_find (y_pre))) ((uf_union_after_find_y (rx)))) X_low_level_spec ) ” 
  &&  “ (equiv (applyf ((uf_union_after_find_x (y_pre))) (rx)) (bind ((uf_find (y_pre))) ((uf_union_after_find_y (rx)))) ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= y_pre) ” 
  &&  “ (y_pre < n_pre) ”
  &&  (IntArray.full parent_pre n_pre ps1 )
  **  (IntArray.full rank_pre n_pre rs1 )
.

Definition uf_union_c_partial_solve_wit_2 := uf_union_c_partial_solve_wit_2_pure -> uf_union_c_partial_solve_wit_2_aux.

Definition uf_union_c_partial_solve_wit_3 := 
forall (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (ps2: (@list Z)) (rs2: (@list Z)) (rx: Z) (ry: Z) ,
  “ (rx <> ry) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps2) (rs2)))) (applyf ((uf_union_after_find_y (rx))) (ry)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps2 )
  **  (IntArray.full rank_pre n_pre rs2 )
|--
  “ (rx <> ry) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps2) (rs2)))) (applyf ((uf_union_after_find_y (rx))) (ry)) X_low_level_spec ) ”
  &&  (((rank_pre + (rx * sizeof(INT) ) )) # Int  |-> (Znth rx rs2 0))
  **  (IntArray.missing_i rank_pre rx 0 n_pre rs2 )
  **  (IntArray.full parent_pre n_pre ps2 )
.

Definition uf_union_c_partial_solve_wit_4 := 
forall (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (ps2: (@list Z)) (rs2: (@list Z)) (rx: Z) (ry: Z) (rx_rank: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (rx_rank = (Znth (rx) (rs2) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps2) (rs2)))) (uf_union_after_rank_rx (rx) (ry) (rx_rank)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps2 )
  **  (IntArray.full rank_pre n_pre rs2 )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (rx_rank = (Znth (rx) (rs2) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps2) (rs2)))) (uf_union_after_rank_rx (rx) (ry) (rx_rank)) X_low_level_spec ) ”
  &&  (((rank_pre + (ry * sizeof(INT) ) )) # Int  |-> (Znth ry rs2 0))
  **  (IntArray.missing_i rank_pre ry 0 n_pre rs2 )
  **  (IntArray.full parent_pre n_pre ps2 )
.

Definition uf_union_c_partial_solve_wit_5 := 
forall (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (ps2: (@list Z)) (rs2: (@list Z)) (rx: Z) (ry: Z) (rx_rank: Z) (ry_rank: Z) ,
  “ (ry_rank < rx_rank) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (rx_rank = (Znth (rx) (rs2) (0))) ” 
  &&  “ (ry_rank = (Znth (ry) (rs2) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps2) (rs2)))) (uf_union_after_rank_ry (rx) (ry) (rx_rank) (ry_rank)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps2 )
  **  (IntArray.full rank_pre n_pre rs2 )
|--
  “ (ry_rank < rx_rank) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (rx_rank = (Znth (rx) (rs2) (0))) ” 
  &&  “ (ry_rank = (Znth (ry) (rs2) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps2) (rs2)))) (uf_union_after_rank_ry (rx) (ry) (rx_rank) (ry_rank)) X_low_level_spec ) ”
  &&  (((parent_pre + (ry * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i parent_pre ry 0 n_pre ps2 )
  **  (IntArray.full rank_pre n_pre rs2 )
.

Definition uf_union_c_partial_solve_wit_6 := 
forall (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (ps2: (@list Z)) (rs2: (@list Z)) (rx: Z) (ry: Z) (rx_rank: Z) (ry_rank: Z) ,
  “ (rx_rank < ry_rank) ” 
  &&  “ (ry_rank >= rx_rank) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (rx_rank = (Znth (rx) (rs2) (0))) ” 
  &&  “ (ry_rank = (Znth (ry) (rs2) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps2) (rs2)))) (uf_union_after_rank_ry (rx) (ry) (rx_rank) (ry_rank)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps2 )
  **  (IntArray.full rank_pre n_pre rs2 )
|--
  “ (rx_rank < ry_rank) ” 
  &&  “ (ry_rank >= rx_rank) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (rx_rank = (Znth (rx) (rs2) (0))) ” 
  &&  “ (ry_rank = (Znth (ry) (rs2) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps2) (rs2)))) (uf_union_after_rank_ry (rx) (ry) (rx_rank) (ry_rank)) X_low_level_spec ) ”
  &&  (((parent_pre + (rx * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i parent_pre rx 0 n_pre ps2 )
  **  (IntArray.full rank_pre n_pre rs2 )
.

Definition uf_union_c_partial_solve_wit_7 := 
forall (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (ps2: (@list Z)) (rs2: (@list Z)) (rx: Z) (ry: Z) (rx_rank: Z) (ry_rank: Z) ,
  “ (rx_rank >= ry_rank) ” 
  &&  “ (ry_rank >= rx_rank) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (rx_rank = (Znth (rx) (rs2) (0))) ” 
  &&  “ (ry_rank = (Znth (ry) (rs2) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps2) (rs2)))) (uf_union_after_rank_ry (rx) (ry) (rx_rank) (ry_rank)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps2 )
  **  (IntArray.full rank_pre n_pre rs2 )
|--
  “ (rx_rank >= ry_rank) ” 
  &&  “ (ry_rank >= rx_rank) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (rx_rank = (Znth (rx) (rs2) (0))) ” 
  &&  “ (ry_rank = (Znth (ry) (rs2) (0))) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps2) (rs2)))) (uf_union_after_rank_ry (rx) (ry) (rx_rank) (ry_rank)) X_low_level_spec ) ”
  &&  (((parent_pre + (rx * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i parent_pre rx 0 n_pre ps2 )
  **  (IntArray.full rank_pre n_pre rs2 )
.

Definition uf_union_c_partial_solve_wit_8 := 
forall (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (uf_state -> Prop))) (ps2: (@list Z)) (rs2: (@list Z)) (rx: Z) (ry: Z) (rx_rank: Z) (ry_rank: Z) ,
  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (rx_rank = ry_rank) ” 
  &&  “ (ry_rank = (Znth (ry) (rs2) (0))) ” 
  &&  “ ((ry_rank + 1 ) <= INT_MAX) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) ((replace_Znth (rx) (ry) (ps2))) (rs2)))) (bump_rank (ry)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre (replace_Znth (rx) (ry) (ps2)) )
  **  (IntArray.full rank_pre n_pre rs2 )
|--
  “ (0 <= rx) ” 
  &&  “ (rx < n_pre) ” 
  &&  “ (0 <= ry) ” 
  &&  “ (ry < n_pre) ” 
  &&  “ (rx <> ry) ” 
  &&  “ (rx_rank = ry_rank) ” 
  &&  “ (ry_rank = (Znth (ry) (rs2) (0))) ” 
  &&  “ ((ry_rank + 1 ) <= INT_MAX) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) ((replace_Znth (rx) (ry) (ps2))) (rs2)))) (bump_rank (ry)) X_low_level_spec ) ”
  &&  (((rank_pre + (ry * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i rank_pre ry 0 n_pre rs2 )
  **  (IntArray.full parent_pre n_pre (replace_Znth (rx) (ry) (ps2)) )
.

Definition uf_union_c_derive_high_level_spec_by_low_level_spec := 
forall (y_pre: Z) (x_pre: Z) (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (repr_of_high_level_spec: (Z -> Z)) (rs_high_level_spec: (@list Z)) (ps_high_level_spec: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (0 <= y_pre) ” 
  &&  “ (y_pre < n_pre) ” 
  &&  “ (uf_abstract (uf_state_of (n_pre) (ps_high_level_spec) (rs_high_level_spec)) repr_of_high_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps_high_level_spec )
  **  (IntArray.full rank_pre n_pre rs_high_level_spec )
|--
EX (ps_low_level_spec: (@list Z)) (rs_low_level_spec: (@list Z)) (X_low_level_spec: (unit -> (uf_state -> Prop))) ,
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (0 <= y_pre) ” 
  &&  “ (y_pre < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps_low_level_spec) (rs_low_level_spec)))) (uf_union (x_pre) (y_pre)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps_low_level_spec )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec ))
  **
  ((EX ps1_2 rs1_2,
  “ (safeExec (equiv ((uf_state_of (n_pre) (ps1_2) (rs1_2)))) (return (tt)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps1_2 )
  **  (IntArray.full rank_pre n_pre rs1_2 ))
  -*
  (EX ps1 rs1 repr_of1,
  “ (uf_abstract (uf_state_of (n_pre) (ps1) (rs1)) repr_of1 ) ” 
  &&  “ (merge (valid ((uf_state_of (n_pre) (ps1) (rs1)))) repr_of_high_level_spec x_pre y_pre repr_of1 ) ”
  &&  (IntArray.full parent_pre n_pre ps1 )
  **  (IntArray.full rank_pre n_pre rs1 )))
.

Definition uf_find_c_derive_low_level_spec_aux_by_low_level_spec := 
forall (B: Type) ,
forall (x_pre: Z) (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (X_low_level_spec_aux: (B -> (uf_state -> Prop))) (c_low_level_spec_aux: (Z -> (@program uf_state B))) (rs_low_level_spec_aux: (@list Z)) (ps_low_level_spec_aux: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps_low_level_spec_aux) (rs_low_level_spec_aux)))) (bind ((uf_find (x_pre))) (c_low_level_spec_aux)) X_low_level_spec_aux ) ”
  &&  (IntArray.full parent_pre n_pre ps_low_level_spec_aux )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec_aux )
|--
EX (ps_low_level_spec: (@list Z)) (rs_low_level_spec: (@list Z)) (X_low_level_spec: (Z -> (uf_state -> Prop))) ,
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps_low_level_spec) (rs_low_level_spec)))) (uf_find (x_pre)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps_low_level_spec )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec ))
  **
  ((EX ps1_2 retval_2,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps1_2) (rs_low_level_spec)))) (return (retval_2)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps1_2 )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec ))
  -*
  (EX ps1 retval,
  “ (0 <= retval) ” 
  &&  “ (retval < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps1) (rs_low_level_spec_aux)))) (applyf (c_low_level_spec_aux) (retval)) X_low_level_spec_aux ) ”
  &&  (IntArray.full parent_pre n_pre ps1 )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec_aux )))
.

Definition uf_find_c_derive_high_level_spec_by_low_level_spec := 
forall (x_pre: Z) (rank_pre: Z) (parent_pre: Z) (n_pre: Z) (repr_of_high_level_spec: (Z -> Z)) (rs_high_level_spec: (@list Z)) (ps_high_level_spec: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (uf_abstract (uf_state_of (n_pre) (ps_high_level_spec) (rs_high_level_spec)) repr_of_high_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps_high_level_spec )
  **  (IntArray.full rank_pre n_pre rs_high_level_spec )
|--
EX (ps_low_level_spec: (@list Z)) (rs_low_level_spec: (@list Z)) (X_low_level_spec: (Z -> (uf_state -> Prop))) ,
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps_low_level_spec) (rs_low_level_spec)))) (uf_find (x_pre)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps_low_level_spec )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec ))
  **
  ((EX ps1_2 retval_2,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < n_pre) ” 
  &&  “ (safeExec (equiv ((uf_state_of (n_pre) (ps1_2) (rs_low_level_spec)))) (return (retval_2)) X_low_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps1_2 )
  **  (IntArray.full rank_pre n_pre rs_low_level_spec ))
  -*
  (EX ps1 retval,
  “ (retval = (repr_of_high_level_spec (x_pre))) ” 
  &&  “ (uf_abstract (uf_state_of (n_pre) (ps1) (rs_high_level_spec)) repr_of_high_level_spec ) ”
  &&  (IntArray.full parent_pre n_pre ps1 )
  **  (IntArray.full rank_pre n_pre rs_high_level_spec )))
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.
Include safeexecE_Strategy_Correct.

Axiom proof_of_uf_find_c_entail_wit_1 : uf_find_c_entail_wit_1.
Axiom proof_of_uf_find_c_entail_wit_2 : uf_find_c_entail_wit_2.
Axiom proof_of_uf_find_c_entail_wit_3 : uf_find_c_entail_wit_3.
Axiom proof_of_uf_find_c_entail_wit_4 : uf_find_c_entail_wit_4.
Axiom proof_of_uf_find_c_return_wit_1 : uf_find_c_return_wit_1.
Axiom proof_of_uf_find_c_return_wit_2 : uf_find_c_return_wit_2.
Axiom proof_of_uf_find_c_partial_solve_wit_1 : uf_find_c_partial_solve_wit_1.
Axiom proof_of_uf_find_c_partial_solve_wit_2_pure : uf_find_c_partial_solve_wit_2_pure.
Axiom proof_of_uf_find_c_partial_solve_wit_2 : uf_find_c_partial_solve_wit_2.
Axiom proof_of_uf_find_c_partial_solve_wit_3 : uf_find_c_partial_solve_wit_3.
Axiom proof_of_uf_union_c_safety_wit_1 : uf_union_c_safety_wit_1.
Axiom proof_of_uf_union_c_safety_wit_2 : uf_union_c_safety_wit_2.
Axiom proof_of_uf_union_c_entail_wit_1 : uf_union_c_entail_wit_1.
Axiom proof_of_uf_union_c_entail_wit_2 : uf_union_c_entail_wit_2.
Axiom proof_of_uf_union_c_entail_wit_3 : uf_union_c_entail_wit_3.
Axiom proof_of_uf_union_c_entail_wit_4 : uf_union_c_entail_wit_4.
Axiom proof_of_uf_union_c_entail_wit_5 : uf_union_c_entail_wit_5.
Axiom proof_of_uf_union_c_entail_wit_6 : uf_union_c_entail_wit_6.
Axiom proof_of_uf_union_c_entail_wit_7 : uf_union_c_entail_wit_7.
Axiom proof_of_uf_union_c_entail_wit_8 : uf_union_c_entail_wit_8.
Axiom proof_of_uf_union_c_entail_wit_9 : uf_union_c_entail_wit_9.
Axiom proof_of_uf_union_c_entail_wit_10 : uf_union_c_entail_wit_10.
Axiom proof_of_uf_union_c_return_wit_1 : uf_union_c_return_wit_1.
Axiom proof_of_uf_union_c_return_wit_2 : uf_union_c_return_wit_2.
Axiom proof_of_uf_union_c_return_wit_3 : uf_union_c_return_wit_3.
Axiom proof_of_uf_union_c_return_wit_4 : uf_union_c_return_wit_4.
Axiom proof_of_uf_union_c_partial_solve_wit_1_pure : uf_union_c_partial_solve_wit_1_pure.
Axiom proof_of_uf_union_c_partial_solve_wit_1 : uf_union_c_partial_solve_wit_1.
Axiom proof_of_uf_union_c_partial_solve_wit_2_pure : uf_union_c_partial_solve_wit_2_pure.
Axiom proof_of_uf_union_c_partial_solve_wit_2 : uf_union_c_partial_solve_wit_2.
Axiom proof_of_uf_union_c_partial_solve_wit_3 : uf_union_c_partial_solve_wit_3.
Axiom proof_of_uf_union_c_partial_solve_wit_4 : uf_union_c_partial_solve_wit_4.
Axiom proof_of_uf_union_c_partial_solve_wit_5 : uf_union_c_partial_solve_wit_5.
Axiom proof_of_uf_union_c_partial_solve_wit_6 : uf_union_c_partial_solve_wit_6.
Axiom proof_of_uf_union_c_partial_solve_wit_7 : uf_union_c_partial_solve_wit_7.
Axiom proof_of_uf_union_c_partial_solve_wit_8 : uf_union_c_partial_solve_wit_8.
Axiom proof_of_uf_union_c_derive_high_level_spec_by_low_level_spec : uf_union_c_derive_high_level_spec_by_low_level_spec.
Axiom proof_of_uf_find_c_derive_low_level_spec_aux_by_low_level_spec : uf_find_c_derive_low_level_spec_aux_by_low_level_spec.
Axiom proof_of_uf_find_c_derive_high_level_spec_by_low_level_spec : uf_find_c_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
