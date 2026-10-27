import R1Z.PV_RunJoin_PathCell0616
import R1Z.PV_RunJoin_FixtureInputCommitment
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathFirst16
open R0P PV_RunJoin_PathModel16
attribute [local irreducible] nodeCompress poseidonPermutation
local notation "leaf" => digestOf PV_RunJoin_FixtureHashModel.s_3_23
theorem prefix_1 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 1 = (![1055864870,1015153496,899228473,2043224478,1075657363,1804637297,712143154,1156362644] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 0 < 24 by decide)]
  change nodeCompress _ _ = _
  trans nodeCompress (![2028667570,45893279,894642502,1930282162,1562116262,823639309,745717450,1034934647] : Fin 8 → Scalar) ![901,918,935,952,969,986,1003,1020]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_6
#print axioms prefix_1
end R1Z.PV_RunJoin_PathFirst16
