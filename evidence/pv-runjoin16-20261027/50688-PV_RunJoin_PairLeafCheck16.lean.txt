import R1Z.PV_RunJoin_PathFirst16
import R1Z.PV_RunJoin_FixtureReturns16
import R1Z.PV_Src_PortParent
import R1Z.PV_RunJoin_OccupiedValidation16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PairLeafCheck16
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_FixtureArguments PV_RunJoin_ShippedExternal
local notation "M" => PV_RunJoin_FixtureRecords.M
attribute [local irreducible] R0P.nodeCompress R0P.poseidonPermutation

def digest : Array U32 8#usize := Array.make 8#usize
  [1055864870#u32,1015153496#u32,899228473#u32,2043224478#u32,1075657363#u32,1804637297#u32,712143154#u32,1156362644#u32]

theorem canonical : Canon8 digest := by intro i hi; interval_cases i <;> decide

theorem parent : @format.pool_v1_tree_parent E_shipped
    witness.pair.pair_leaf.first_commitment witness.pair.pair_leaf.second_commitment = ok digest := by
  apply PV_Src_PortParent.source
  · decide
  · exact canonical
  · have left : digK (K := M) witness.pair.pair_leaf.first_commitment =
        ![2028667570,45893279,894642502,1930282162,1562116262,823639309,745717450,1034934647] := by
      funext i; fin_cases i <;> rfl
    have right : digK (K := M) witness.pair.pair_leaf.second_commitment =
        ![901,918,935,952,969,986,1003,1020] := by
      funext i; fin_cases i <;> rfl
    have target : digK (K := M) digest =
        ![1055864870,1015153496,899228473,2043224478,1075657363,1804637297,712143154,1156362644] := by
      funext i; fin_cases i <;> rfl
    change R0P.nodeCompress (digK (K := M) _) (digK (K := M) _) = digK (K := M) digest
    rw [left,right,target]
    exact PV_RunJoin_PathModel16.node_6

theorem validate : pair_tree_profile.PoolV1PairLeafWitnessV1.validate witness.pair.pair_leaf = ok (.Ok ()) := by
  apply PV_RunJoin_OccupiedValidation16.validates
  · exact PV_RunJoin_FixtureAdmission.first
  · exact PV_RunJoin_FixtureAdmission.second
  · decide
  · decide
  · with_unfolding_all rfl

theorem leaf : @pair_tree_profile.PoolV1PairLeafWitnessV1.leaf_digest E_shipped
    witness.pair.pair_leaf = ok (.Ok digest) := by
  unfold R1Z.BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.leaf_digest
  rw [validate]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  rw [parent]; rfl
#print axioms canonical
#print axioms parent
#print axioms validate
#print axioms leaf
end R1Z.PV_RunJoin_PairLeafCheck16
