import NEB_SquareDomains
set_option autoImplicit false
noncomputable section
namespace NEB_SquareComposition
open Aeneas Aeneas.Std Result AspisR1

/-- Arbitrary reached scalar operands satisfy the selected all-raw multiply
packet, with the SAME operand twice and no canonical-input strengthening. -/
theorem cell (before : U32) : ∃ after : U32,
    FIo_Native.aspis_core.field.M31.mul before before=ok after ∧
    after.val=(before.val*before.val)%2147483647 ∧ after.val<2147483647 :=
  LPf_BaseMultiply.source before before

/-- The inherited actual Range.next native step is paired with the existing
trace induction. No complete native trace or output equality is assumed here. -/
theorem loop_frame {S Event : Type} (state : S) (count : Usize) (before : U32) :
    ∃ after : U32,
      NBG_SquareTrace.Trace count.val before after ∧
      AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul before count=ok after ∧
      NEB_PureFrame.run (Event:=Event) state
        (AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul before count)=ok (after,state,[]) ∧
      (0<count.val → after.val<2147483647) := by
  obtain ⟨after,call,trace,canonical⟩ := NEB_SquareDomains.source before count
  exact ⟨after,trace,call,by rw [call];rfl,canonical⟩

/-- A SAME arbitrary-range trace, supplied one native scalar cell at a time,
identifies the emitted Result and the complete pure frame without an extra
successful-return premise. Range.start need not be zero. -/
theorem trace_frame {S Event : Type} (state : S) (n : Nat) (before after : U32)
    (iter : core.ops.range.Range Usize)
    (length : iter.end.val-iter.start.val=n)
    (trace : NBG_SquareTrace.Trace n before after) :
    AspisR1M31Inverse.field.square_n_loop FIo_Native.aspis_core.field.M31.mul iter before=ok after ∧
    NEB_PureFrame.run (Event:=Event) state
      (AspisR1M31Inverse.field.square_n_loop FIo_Native.aspis_core.field.M31.mul iter before)=ok (after,state,[]) := by
  have call := NBG_SquareTrace.loop_result trace iter length
  exact ⟨call,by rw [call];rfl⟩

#print axioms cell
#print axioms loop_frame
#print axioms trace_frame
end NEB_SquareComposition
end
