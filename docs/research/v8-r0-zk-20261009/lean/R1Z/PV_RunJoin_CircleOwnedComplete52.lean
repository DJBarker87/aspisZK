import R1Z.PV_RunJoin_CircleOwnedSampler52
import R1Z.PV_RunJoin_CircleOwnedFallback52
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RunJoin_CircleOwnedComplete52
open PV_RunJoin_CircleOwnedCarrier52

def encRow (second : Bool) : PV_AL_CircleOwned.aspis_core.r0_transcript.CircleRow :=
  if second then .Second else .First

/-- Both row values, every block, with the actual fallback and every outer Result. -/
theorem complete (block : Array U8 32#usize) (second : Bool) :
    PV_AL_CircleOwned.circle_owned block (encRow second) = (do
      let p ← PV_RunJoin_CircleRawMap52.circle_owned block second
      ok (encPoint p)) := by
  unfold PV_AL_CircleOwned.circle_owned PV_RunJoin_CircleRawMap52.circle_owned
  rw [PV_RunJoin_CircleOwnedSampler52.s7]
  simp only [bind_assoc_eq,bind_tc_ok]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro parameter _
  rw [PV_RunJoin_CircleOwnedMap52.complete]
  simp only [bind_assoc_eq,bind_tc_ok]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro r _
  cases r with
  | Ok p => rfl
  | Err e =>
    cases second <;> cases e <;> simp only [encRow,PV_RunJoin_CircleOwnedMap52.encOutcome,
      PV_RunJoin_CircleOwnedMap52.encError,Bool.false_eq_true,if_false,if_true,
      PV_RunJoin_CircleOwnedFallback52.first,PV_RunJoin_CircleOwnedFallback52.second]

#print axioms encRow
#print axioms complete
end R1Z.PV_RunJoin_CircleOwnedComplete52
