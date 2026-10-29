import NBG_SquareTrace
import NEB_PureFrame
set_option autoImplicit false
noncomputable section
namespace NEB_SquareDomains
open Aeneas Aeneas.Std Result AspisR1

theorem preserve {n : Nat} {before after : U32}
    (trace : NBG_SquareTrace.Trace n before after) (canonical : before.val<2147483647) :
    after.val<2147483647 := by
  induction trace with
  | done value => exact canonical
  | @step n before middle after cell tail ih =>
    have cm : middle.val<2147483647 := by rw [cell];exact Nat.mod_lt _ (by decide)
    exact ih cm

theorem positive {n : Nat} {before after : U32}
    (trace : NBG_SquareTrace.Trace n before after) (nonempty : 0<n) :
    after.val<2147483647 := by
  cases trace with
  | done value => omega
  | step cell tail =>
    apply preserve tail
    rw [cell]
    exact Nat.mod_lt _ (by decide)

theorem trace_exists (n : Nat) (before : U32) :
    ∃ after, NBG_SquareTrace.Trace n before after := by
  induction n generalizing before with
  | zero => exact ⟨before,.done before⟩
  | succ n ih =>
    obtain ⟨middle,run,value,_⟩ := LPf_BaseMultiply.source before before
    obtain ⟨after,tail⟩ := ih middle
    exact ⟨after,.step value tail⟩

/-- All raw initial words are allowed. Canonicality is derived after a positive
number of iterations, never imposed on the zero-iteration return. -/
theorem source (before : U32) (count : Usize) :
    ∃ after, AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul before count=ok after ∧
      NBG_SquareTrace.Trace count.val before after ∧
      (0<count.val → after.val<2147483647) := by
  obtain ⟨after,trace⟩ := trace_exists count.val before
  exact ⟨after,NBG_SquareTrace.native_result count before after trace,trace,positive trace⟩

#print axioms preserve
#print axioms positive
#print axioms trace_exists
#print axioms source
end NEB_SquareDomains
end
