import JFv_World
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_WorldAdmission
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open JFv_World

theorem first (proofAccount : Slice U8) : S2W_D189Consolidation.RuntimeEntrypointAdmission
    (model (Nat → Record)) (e1 proofAccount) (e1 proofAccount).heap 3 := by
  apply CPH_FixtureEntry.admitted
  · intro a
    change a ≠ a+100
    omega
  · intro a small
    change a<8
    omega
  · intro c
    rfl

theorem second (proofAccount : Slice U8) : S2W_D189Consolidation.RuntimeEntrypointAdmission
    (model (Nat → Record)) (e2 proofAccount) (e2 proofAccount).heap 7 := by
  apply CPH_FixtureEntry.admitted
  · intro a
    change CPH_FixtureData.readerCell a ≠ CPH_FixtureData.readerCell a+100
    omega
  · intro a small
    exact CPH_FixtureAdmission.reader_bound a small
  · intro c
    rfl

theorem trusted : S2TrustedSdkBorrow (model (Nat → Record)) ∧
    S2W_TrustedStd.TrustedStd CPH_FixtureData.copy :=
  ⟨model_satisfies _,S2W_TrustedStd.specification_satisfies _⟩

#print axioms first
#print axioms second
#print axioms trusted
end AspisR1.JFv_WorldAdmission
end
