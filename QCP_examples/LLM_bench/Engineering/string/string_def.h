#include "verification_list.h"
#include "char_array_def.h"

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Engineering.string.string_lib */

/*@ Extern Coq (store_string : Z -> list Z -> Assertion)
               (all_ascii : list Z -> Prop)
               (no_inner_nul : list Z -> Prop)
               (valid_string : list Z -> Prop)
               (c_string : list Z -> list Z)
               (string_length : list Z -> Z)
 */

/*@ include strategies "string.strategies" */
