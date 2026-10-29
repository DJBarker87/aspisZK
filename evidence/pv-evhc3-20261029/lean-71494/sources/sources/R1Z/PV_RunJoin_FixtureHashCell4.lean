import R1Z.PV_RunJoin_FixtureHashRound4_0
import R1Z.PV_RunJoin_FixtureHashRound4_1
import R1Z.PV_RunJoin_FixtureHashRound4_2
import R1Z.PV_RunJoin_FixtureHashRound4_3
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureHashModel
open R0P
theorem permutation_4 : poseidonPermutation s_4_0 = s_4_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_4_1,round_4_2,round_4_3,round_4_4,round_4_5,round_4_6,round_4_7,round_4_8,round_4_9,round_4_10,round_4_11,round_4_12,round_4_13,round_4_14,round_4_15,round_4_16,round_4_17,round_4_18,round_4_19,round_4_20,round_4_21,round_4_22,round_4_23]
#print axioms permutation_4
end R1Z.PV_RunJoin_FixtureHashModel
