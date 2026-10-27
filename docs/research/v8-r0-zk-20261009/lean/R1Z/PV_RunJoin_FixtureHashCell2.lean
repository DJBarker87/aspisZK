import R1Z.PV_RunJoin_FixtureHashRound2_0
import R1Z.PV_RunJoin_FixtureHashRound2_1
import R1Z.PV_RunJoin_FixtureHashRound2_2
import R1Z.PV_RunJoin_FixtureHashRound2_3
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureHashModel
open R0P
theorem permutation_2 : poseidonPermutation s_2_0 = s_2_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_2_1,round_2_2,round_2_3,round_2_4,round_2_5,round_2_6,round_2_7,round_2_8,round_2_9,round_2_10,round_2_11,round_2_12,round_2_13,round_2_14,round_2_15,round_2_16,round_2_17,round_2_18,round_2_19,round_2_20,round_2_21,round_2_22,round_2_23]
#print axioms permutation_2
end R1Z.PV_RunJoin_FixtureHashModel
