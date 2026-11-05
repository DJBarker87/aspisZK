import NHE_ScalarCell
set_option autoImplicit false
namespace NHE_ScalarStep
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

def step (p : Array NE 4#usize) (f : Array NQ 4#usize) (carry : NE) (s : Usize) : Result (NE × (Array NE 4#usize × Array NQ 4#usize)) := do
 let index ← Array.index_usize FIo_Native.weights.PERM s
 let value ← Array.index_usize p index
 let scalar ← Array.index_usize f s
 let out ← NHE_ScalarCell.run value scalar carry
 ok (out,(p,f))

theorem emitted (p : Array NE 4#usize) (f : Array NQ 4#usize) (carry : NE) (s : Usize) :
 step p f carry s=
 FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut (p,f) (carry,s) := rfl

/-- A local selected-cell association. Array selection identities must be derived
by the future four-step caller invariant; this is not a scalar_factor closure. -/
theorem observed (p : Array NE 4#usize) (f : Array NQ 4#usize) (carry value : NE) (scalar : NQ) (s index : Usize)
 (hi : Array.index_usize FIo_Native.weights.PERM s=ok index)
 (hv : Array.index_usize p index=ok value) (hs : Array.index_usize f s=ok scalar)
 (cv : canonE value) (cs : canonQ scalar) (cc : canonE carry) :
 ∃ out, step p f carry s=ok (out,(p,f)) ∧ canonE out := by
 obtain ⟨product,out,hp,cp,run,co,reference⟩ := NHE_ScalarCell.total value scalar carry cv cs cc
 exact ⟨out,by simp only [step,hi,hv,hs,run,bind_tc_ok],co⟩

#print axioms emitted
#print axioms observed
end NHE_ScalarStep
