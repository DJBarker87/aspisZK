import NLC_Ready
set_option autoImplicit false
namespace AspisR1.NLC_Finish
/-- Exactly the optional slots read by each source-interpreter arm. Nested
markers have no optional reads and are excluded from initial invocations by Major. -/
def ReadsReady {H : Type} (s : State H) : Prop :=
 let l := s.locals
 match s.next with
 | .terminal => l.claims.isSome = true ∧ l.alpha.isSome = true
 | .mapPublic => l.terminalReply.isSome = true
 | .lowArray | .highArray | .blind => l.claims.isSome = true
 | .alpha => l.alpha.isSome = true
 | .mask => l.low.isSome = true ∧ l.high.isSome = true ∧ l.blind.isSome = true ∧ l.alpha.isSome = true
 | .decode25 => l.record25.isSome = true
 | .multiply => l.terminal.isSome = true
 | .addMask => l.mask.isSome = true ∧ l.product.isSome = true
 | .extra28 => l.extra.isSome = true
 | .addExtra => l.partialValue.isSome = true ∧ l.extraCell.isSome = true
 | .terminalGuard => l.running.isSome = true ∧ l.masked.isSome = true
 | .stateBefore => l.transcript.isSome = true
 | .circle0 => l.transcript.isSome = true ∧ l.record25.isSome = true
 | .decode26 => l.record26.isSome = true
 | .circle1 => l.transcript.isSome = true ∧ l.record26.isSome = true
 | .circleGuard => l.z0.isSome = true ∧ l.z1.isSome = true
 | .rootCopy => l.payload.isSome = true
 | .verified => l.root.isSome = true ∧ l.alpha.isSome = true ∧ l.claims.isSome = true ∧
   l.extra.isSome = true ∧ l.beforeZ1.isSome = true ∧ l.stateBefore.isSome = true ∧
   l.z0.isSome = true ∧ l.z1.isSome = true ∧ l.transcript.isSome = true
 | _ => True

theorem ready_reads {H : Type} (s : State H) (before : Ready s) : ReadsReady s := by
 cases atSite : s.next <;> simp_all [Ready,ReadsReady,rank]

/-- A demanded source slot has a value, so its read cannot introduce the
interpreter's missing-slot fault. This is not a native ownership theorem. -/
theorem initialized_read {A : Type} (slot : Option A) (initialized : slot.isSome = true) :
 ∃ value, NLC_Finish.read slot = Aeneas.Std.Result.ok value := by
 cases slot with
 | none => cases initialized
 | some value => exact ⟨value,rfl⟩
#print axioms ready_reads
#print axioms initialized_read
end AspisR1.NLC_Finish
