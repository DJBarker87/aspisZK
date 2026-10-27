import R1Z.ProverRw18ContextInduction
import R1Z.PV_RW_CombinedCompression
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18ContextCompression
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRw18InlineContext
variable [ExternalTypes]

def compress [ExternalFuns] (tag : U32) (values : Slice U32) (lambda : Q) : Result Q := do
  let complex ← aspis_core.field.CM31.from_m31 tag
  let out ← aspis_core.field.QM31.from_cm31 complex
  let iterator ← SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter values
  ProverRw18InlineContext.run lambda iterator out lambda

-- This compares contexts. The source identity for the original whole helper
-- is deliberately not manufactured by naming this context `compress`.
theorem combined (ops : ExternalFuns) (tag : U32) (values : Slice U32) (lambda : Q) :
    @compress _ (PV_CurrentScaleInstall.selected ops) tag values lambda =
      PV_RW_CombinedCompression.compress ops tag values lambda := by
  unfold compress PV_RW_CombinedCompression.compress
  change (do
    let complex ← (PV_CurrentScaleInstall.selected ops).op61 tag
    let out ← (PV_CurrentScaleInstall.selected ops).op66 complex
    let iterator ← SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter values
    @ProverRw18InlineContext.run _ (PV_CurrentScaleInstall.selected ops) lambda iterator out lambda) = _
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro complex _
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro out _
  rw [PV_RW_IteratorSource.start]
  simp only [bind_tc_ok]
  rw [PV_RW_IteratorStateLoop.control]
  exact @ProverRw18ContextInduction.run _ (PV_CurrentScaleInstall.selected ops)
    lambda values 0 out lambda

theorem owned (ops : ExternalFuns) (tag : U32) (values : Slice U32) (lambda : Q) :
    @compress _ (PV_CurrentScaleInstall.selected ops) tag values lambda =
      PV_RW_CompressClosed.owned tag values lambda :=
  (combined ops tag values lambda).trans (PV_RW_CombinedCompression.owned ops tag values lambda)

#print axioms combined
#print axioms owned
end R1Z.ProverRw18ContextCompression
