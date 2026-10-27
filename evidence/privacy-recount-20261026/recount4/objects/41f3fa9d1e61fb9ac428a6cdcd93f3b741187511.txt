import R1Z.PV_RW_IteratorStateLoop
import R1Z.PV_RW_CompressNativeTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CombinedCompression
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Q := aspis_core.field.QM31
variable [ExternalTypes]

-- The source-composed compression using the emitted combined transition.
-- Association to the original whole Rust helper remains OPEN.
def compress (ops : ExternalFuns) (tag : U32) (values : Slice U32) (lambda : Q) : Result Q := do
  let complex ← (PV_CurrentScaleInstall.selected ops).op61 tag
  let initial ← (PV_CurrentScaleInstall.selected ops).op66 complex
  let iterator ← SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter values
  let state ← PV_RW_IteratorStateLoop.run ops lambda iterator (initial,lambda)
  ok state.1

theorem control (ops : ExternalFuns) (tag : U32) (values : Slice U32) (lambda : Q) :
    compress ops tag values lambda=PV_RW_CompressNativeControl.source ops tag values lambda := by
  unfold compress PV_RW_CompressNativeControl.source
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro complex _
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro initial _
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro iterator _
  rw [PV_RW_IteratorStateLoop.control]
  rfl

theorem owned (ops : ExternalFuns) (tag : U32) (values : Slice U32) (lambda : Q) :
    compress ops tag values lambda=PV_RW_CompressClosed.owned tag values lambda :=
  (control ops tag values lambda).trans (PV_RW_CompressNativeControl.owned ops tag values lambda)

theorem arity16 (ops : ExternalFuns) (tag : U32) (values : Array U32 16#usize) (lambda : Q) :
    compress ops tag (Array.to_slice values) lambda=
      PV_RW_CompressClosed.owned tag (Array.to_slice values) lambda := owned ops tag _ lambda

theorem total (ops : ExternalFuns) (tag : U32) (values : Slice U32) (lambda : Q) :
    ∃ final, compress ops tag values lambda=ok final := by
  rw [control]
  exact PV_RW_CompressNativeTotal.output ops tag values lambda
#print axioms control
#print axioms owned
#print axioms arity16
#print axioms total
end R1Z.PV_RW_CombinedCompression
