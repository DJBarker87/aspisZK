import R1Z.PV_Src_FixtureCommonValidation

/-! Nominal identities before source-validator composition. Keeping these
separate prevents elaboration from unfolding concrete fixture hash terms. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_FixtureValidationInputs
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort.pool_v1 PV_Src_CheckedFixtures

variable (s : pair_tree_profile.PoolV1PairLiveSnapshotV1)
  (c : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (a : Array U32 8#usize)

theorem transfer_pair (p : BuilderPublicProjection.Transfer) :
    PV_Src_CheckedValidation.sourcePair (transferInput p 0x54321#u32 s c a) =
      PV_Src_FixturePairValidation.sourcePair false := rfl

theorem withdrawal_pair (p : BuilderPublicProjection.Withdrawal) :
    PV_Src_CheckedValidation.sourcePair (withdrawalInput p 0x54321#u32 s c a) =
      PV_Src_FixturePairValidation.sourcePair true := rfl

theorem transfer_values (p : BuilderPublicProjection.Transfer) :
    PV_Src_NativeInput.outputValue (transferInput p 0x54321#u32 s c a).request = 600#u32 ∧
      (transferInput p 0x54321#u32 s c a).change.value = 400#u32 := ⟨rfl,rfl⟩

theorem withdrawal_values (p : BuilderPublicProjection.Withdrawal) :
    PV_Src_NativeInput.outputValue (withdrawalInput p 0x54321#u32 s c a).request = 250#u32 ∧
      (withdrawalInput p 0x54321#u32 s c a).change.value = 750#u32 := ⟨rfl,rfl⟩

theorem input_value (withdrawal : Bool) :
    (PV_Src_FixturePairValidation.sourcePair withdrawal).value = 1000#u32 := rfl

#print axioms transfer_pair
#print axioms withdrawal_pair
#print axioms transfer_values
#print axioms withdrawal_values
#print axioms input_value
end R1Z.PV_Src_FixtureValidationInputs
