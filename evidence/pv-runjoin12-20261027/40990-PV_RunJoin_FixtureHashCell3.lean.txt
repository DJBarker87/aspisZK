import R1Z.PV_RunJoin_FixtureHashRound3_0
import R1Z.PV_RunJoin_FixtureHashRound3_1
import R1Z.PV_RunJoin_FixtureHashRound3_2
import R1Z.PV_RunJoin_FixtureHashRound3_3
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureHashModel
open R0P
theorem permutation_3 : poseidonPermutation s_3_0 = s_3_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_3_1,round_3_2,round_3_3,round_3_4,round_3_5,round_3_6,round_3_7,round_3_8,round_3_9,round_3_10,round_3_11,round_3_12,round_3_13,round_3_14,round_3_15,round_3_16,round_3_17,round_3_18,round_3_19,round_3_20,round_3_21,round_3_22,round_3_23]
#print axioms permutation_3
end R1Z.PV_RunJoin_FixtureHashModel
