import R1Z.PV_CBL_BlockFourValue
import R1Z.PV_CBL_BlockScheduleValue
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_BlockValueBoundary
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar PV_CBL_FallbackRoundsModel
set_option autoImplicit false
/-- Symbolic boundaries prevent tactic matching from evaluating SHA state. -/
@[irreducible] def four (s : State) (w k : A4) : State := PV_CBL_BlockFourValue.value s w k
@[irreducible] def schedule (a b c d : A4) : A4 := PV_CBL_BlockScheduleValue.value a b c d
theorem four_source (s : State) (w k : A4) :
    PV_CBL_FallbackFourModel.source (pack s.a s.b s.e s.f) (pack s.c s.d s.g s.h) w k =
      ok (packed (four s w k)) := by
  unfold four
  exact PV_CBL_BlockFourValue.source s w k
theorem schedule_source (a b c d : A4) :
    PV_CBL_FallbackBlock.sha_fallback_reference.schedule a b c d = ok (schedule a b c d) := by
  unfold schedule
  exact PV_CBL_BlockScheduleValue.source a b c d
theorem packed_bind {X : Type} (s : State) (K : A4 → A4 → Result X) :
    (do let (a,c) ← ok (packed s); K a c) =
      K (pack s.a s.b s.e s.f) (pack s.c s.d s.g s.h) := rfl
#print axioms four
#print axioms schedule
#print axioms four_source
#print axioms schedule_source
#print axioms packed_bind
end R1Z.PV_CBL_BlockValueBoundary
