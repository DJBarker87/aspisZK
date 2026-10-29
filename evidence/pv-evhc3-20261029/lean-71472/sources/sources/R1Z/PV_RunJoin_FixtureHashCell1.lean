import R1Z.PV_RunJoin_FixtureHashRound1_0
import R1Z.PV_RunJoin_FixtureHashRound1_1
import R1Z.PV_RunJoin_FixtureHashRound1_2
import R1Z.PV_RunJoin_FixtureHashRound1_3
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureHashModel
open R0P
theorem permutation_1 : poseidonPermutation s_1_0 = s_1_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_1_1,round_1_2,round_1_3,round_1_4,round_1_5,round_1_6,round_1_7,round_1_8,round_1_9,round_1_10,round_1_11,round_1_12,round_1_13,round_1_14,round_1_15,round_1_16,round_1_17,round_1_18,round_1_19,round_1_20,round_1_21,round_1_22,round_1_23]
#print axioms permutation_1
end R1Z.PV_RunJoin_FixtureHashModel
