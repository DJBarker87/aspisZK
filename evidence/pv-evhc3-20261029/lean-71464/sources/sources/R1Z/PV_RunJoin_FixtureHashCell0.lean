import R1Z.PV_RunJoin_FixtureHashRound0_0
import R1Z.PV_RunJoin_FixtureHashRound0_1
import R1Z.PV_RunJoin_FixtureHashRound0_2
import R1Z.PV_RunJoin_FixtureHashRound0_3
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureHashModel
open R0P
theorem permutation_0 : poseidonPermutation s_0_0 = s_0_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_0_1,round_0_2,round_0_3,round_0_4,round_0_5,round_0_6,round_0_7,round_0_8,round_0_9,round_0_10,round_0_11,round_0_12,round_0_13,round_0_14,round_0_15,round_0_16,round_0_17,round_0_18,round_0_19,round_0_20,round_0_21,round_0_22,round_0_23]
#print axioms permutation_0
end R1Z.PV_RunJoin_FixtureHashModel
