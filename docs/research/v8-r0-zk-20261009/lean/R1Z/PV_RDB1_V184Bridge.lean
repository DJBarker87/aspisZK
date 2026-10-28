import R1Z.PV_RDB1_V184
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_V184Bridge
open PV_RDB1_Pointer

/-- The changed deployed cast, followed by the complete native world
execution. Cast is sequenced explicitly; no successful-result premise. -/
def deployed {T P F : Type} (p : NonNull T P)
    (b : PV_RDB1_V184_PopWorld.Buffer T) (w : PV_RDB1_V184_PopWorld.World)
    (memory : PV_RDB1_V184_MoveMemory.Memory) (frame : F) :
    Result (NonNull T P × PV_RDB1_V184_MoveMemory.Observation T F) := do
  let (q, w') ← ok (deployedCast (U := T) p, w)
  let o ← PV_RDB1_V184_MoveWorld.nativeWorld b w' memory frame
  ok (q,o)

theorem complete {T P F : Type} (p : NonNull T P)
    (b : PV_RDB1_V184_PopWorld.Buffer T) (w : PV_RDB1_V184_PopWorld.World)
    (memory : PV_RDB1_V184_MoveMemory.Memory) (frame : F) (width : Nat) :
    ∃ o, deployed p b w memory frame = ok (historicalCast p,o) ∧
      PV_RDB1_V184_MoveWorld.referenceWorld b w memory frame width = ok o ∧
      o.returned = b.value.val.getLast? ∧ o.remaining.val = b.value.val.dropLast ∧
      o.buffer = b.address ∧ o.capacity = b.capacity ∧ o.world = w ∧
      o.memory = memory ∧ o.frame = frame := by
  obtain ⟨o, hn, hr, h⟩ := PV_RDB1_V184.complete b w memory frame width
  refine ⟨o, ?_, hr, h⟩
  unfold deployed
  rw [cast_complete]
  change (do let out ← PV_RDB1_V184_MoveWorld.nativeWorld b w memory frame
             ok (historicalCast p, out)) = ok (historicalCast p, o)
  rw [hn]
  rfl

#print axioms complete
end R1Z.PV_RDB1_V184Bridge
