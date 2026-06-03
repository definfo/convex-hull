From SimpleC.EE.LLM_bench.Algorithms.manacher Require Import manacher_goal manacher_proof_auto manacher_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include manacher_proof_auto.
  Include manacher_proof_manual.
End VC_Correctness.
