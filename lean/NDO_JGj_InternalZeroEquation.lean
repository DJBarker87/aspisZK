import NDO_JGj_ZeroSubtract
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_InternalZeroEquation
open Aeneas Aeneas.Std Result FIq_Native
open JGj_RawBounds
abbrev Callback := state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64
/-- Keep the source's explicit lifts and source order in the equation. -/
theorem source (a : Raw) (w : Words) (i : Usize) :
    Callback.call_mut (a,w) i=(do
      let x ← Array.index_usize a i
      let p ← lift (core.convert.num.FromU64U32.from field.P)
      let withP ← x+p
      let y ← Array.index_usize w i
      let wide ← lift (core.convert.num.FromU64U32.from y)
      let out ← withP-wide
      ok (out,(a,w))) := by rfl
#print axioms source
end AspisR1.JGj_InternalZeroEquation
end
