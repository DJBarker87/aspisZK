import R1Z.PV_RunJoin_FixtureArguments
import R1Z.PV_Src_CanonicalRoots

/-! Compare only the finite frozen root literals to the fixture snapshot.
No generating recurrence is evaluated and no compiler selection is inferred. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_FixtureRootWords
open Aeneas Aeneas.Std Result R0Z.WriterRefine

theorem frontier : BuilderRecordsPublic.empty20 PV_Src_CanonicalRoots.table =
    PV_RunJoin_FixtureArguments.snapshot.frontier := by
  apply BuilderRecordCanonical.array_ext
  intro l hl
  have hl20 : l < 20 := by simpa using hl
  rw [BuilderRecordsPublic.empty20,BuilderRecordsArray.tabulate_get _ _ _ hl]
  rw [PV_Src_CanonicalRoots.at_level ⟨l,by omega⟩]
  apply BuilderRecordCanonical.array_ext
  intro j hj
  have hj8 : j < 8 := by simpa using hj
  rw [arr8_get _ j hj8]
  unfold PV_Src_CanonicalRoots.word R0P.emptyRootsNat
  interval_cases l <;> interval_cases j <;> rfl

#print axioms frontier
end R1Z.PV_RunJoin_FixtureRootWords
