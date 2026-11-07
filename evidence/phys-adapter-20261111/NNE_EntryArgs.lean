import NNE_Route
set_option autoImplicit false
noncomputable section
namespace NNE_EntryArgs
open Aeneas Aeneas.Std AspisR1 S2W_D189Entry S2W_ReturnedCheckpoint

def args (e : Entry) (count : Nat) (program : S2W_ExtractionBoundary.Program)
 (data : Slice U8) : RSL.TX2_240.Args :=
 ⟨NNE_Entry.key program,(List.range count).map (NNE_Entry.account e),nativeBytes data⟩

theorem count (e : Entry) (n : Nat) (p : S2W_ExtractionBoundary.Program) (data : Slice U8) :
 (args e n p data).accounts.length = n := by simp [args]

theorem stage1_test (data : Slice U8) :
 RSL.TX2_221.stage1Route (nativeBytes data) = true ↔ Hiq_ReleaseRoute.stage1 data := by
 rw [NNE_Route.stage1]
 simp [RSL.TX2_221.stage1Route]

theorem first_route (e : Entry) (p : S2W_ExtractionBoundary.Program) (data : Slice U8)
 (selected : Hiq_ReleaseRoute.stage1 data) :
 RSL.TX2_221.stage1Route (args e 3 p data).data = true :=
 (stage1_test data).mpr selected

theorem second_route (e : Entry) (p : S2W_ExtractionBoundary.Program) (data : Slice U8)
 (selected : Hiq_ReleaseRoute.asq8 data) :
 (args e 7 p data).data.take 4 = RSL.REQUEST_MAGIC :=
 (NNE_Route.asq8 data).mp selected

/-- Counts and data route are separate from allocator private transitions. -/
theorem first_guard (e : Entry) (p : S2W_ExtractionBoundary.Program) (data : Slice U8)
 (selected : Hiq_ReleaseRoute.stage1 data) : RSL.TX1_344.badRoute (args e 3 p data) = false := by
 apply (NNE_Route.first_guard _ _ data).mpr
 exact ⟨selected,by simp [args]⟩

theorem second_guard (e : Entry) (p : S2W_ExtractionBoundary.Program) (data : Slice U8)
 (selected : Hiq_ReleaseRoute.asq8 data) : RSL.TX2_240.badRoute (args e 7 p data) = false := by
 apply (NNE_Route.second_guard _ _ data).mpr
 exact ⟨selected,by simp [args]⟩
#print axioms count
#print axioms stage1_test
#print axioms first_route
#print axioms second_route
#print axioms first_guard
#print axioms second_guard
end NNE_EntryArgs
end
