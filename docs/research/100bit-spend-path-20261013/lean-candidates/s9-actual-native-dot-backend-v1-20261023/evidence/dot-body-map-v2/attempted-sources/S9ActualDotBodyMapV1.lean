import AspisR1S9ProductionPairCutV1.Funs
import OriginalDotPushRawLoopToLiteralV1
import S9LoopSuccessTransportV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ActualDotBodyMapV1
open AspisR1S9SourceResultTransportV1 AspisR1S9LoopSuccessTransportV1
abbrev NativeDot := AspisR1S9ProductionPairCutV1.fast_pairing.canonical.Dot
abbrev OldDot := AspisR1DotPushOriginalRaw.Proof.SourceDot
abbrev Iter := core.ops.range.Range Usize

def toOld (s : NativeDot) : OldDot := ⟨s.sums⟩
def stateToOld (s : Iter × NativeDot) : Iter × OldDot := (s.1,toOld s.2)

theorem mapResult_bind_id {A B C : Type} (f : B → C) (m : Result A) (next : A → Result B) :
    mapResult f (m >>= next) = (m >>= fun a => mapResult f (next a)) := by
  cases m <;> rfl

/-- The current exact emitted update body preserves the old concrete raw-loop
transition, including arbitrary accumulator/raw words and rejected indexing.
The fixed31 shift has identical checked/wrapping behavior. -/
theorem actual_dot_body_map (raw : Array U64 4#usize) (iter : Iter) (s : NativeDot) :
    mapResult (mapFlow stateToOld toOld)
      (AspisR1S9ProductionPairCutV1.fast_pairing.canonical.Dot.push_loop.body raw iter s) =
    AspisR1DotPushOriginalRaw.Proof.body raw iter (toOld s) := by
  unfold AspisR1S9ProductionPairCutV1.fast_pairing.canonical.Dot.push_loop.body
    AspisR1DotPushOriginalRaw.Proof.body
    AspisR1EbyKDotPushSourceV1.fast_pairing.canonical.Dot.push_loop.body
  simp only [mapResult_bind_id]
  congr 1
  funext next
  rcases next with ⟨o,iterNext⟩
  cases o with
  | none => rfl
  | some j => rfl

#print axioms actual_dot_body_map
end AspisR1S9ActualDotBodyMapV1
