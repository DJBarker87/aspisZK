import R1Z.PV_RunJoin_FixtureHashRound5_0
import R1Z.PV_RunJoin_FixtureHashRound5_1
import R1Z.PV_RunJoin_FixtureHashRound5_2
import R1Z.PV_RunJoin_FixtureHashRound5_3
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureHashModel
open R0P
theorem permutation_5 : poseidonPermutation s_5_0 = s_5_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_5_1,round_5_2,round_5_3,round_5_4,round_5_5,round_5_6,round_5_7,round_5_8,round_5_9,round_5_10,round_5_11,round_5_12,round_5_13,round_5_14,round_5_15,round_5_16,round_5_17,round_5_18,round_5_19,round_5_20,round_5_21,round_5_22,round_5_23]
#print axioms permutation_5
end R1Z.PV_RunJoin_FixtureHashModel
