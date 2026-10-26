import R1Z.ProverRw18ContextCompression
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18OriginalLift
open Aeneas Aeneas.Std Result ProverRwFull
section Emitted
variable [ExternalTypes] [ExternalFuns]
/-- [aspis_statement::logup::lift]:
    Source: 'crates/aspis-statement/src/logup.rs', lines 69:0-71:1 -/
def logup.lift
  (value : aspis_core.field.M31) : Result aspis_core.field.QM31 := do
  let c ← aspis_core.field.CM31.from_m31 value
  aspis_core.field.QM31.from_cm31 c

end Emitted
variable [ExternalTypes]

theorem initial (ops : ExternalFuns) (tag : U32) :
    @logup.lift _ (PV_CurrentScaleInstall.selected ops) tag=
      ok (PV_RW_CompressLiftSelectors.initial tag) := by
  unfold logup.lift
  change (do
    let c ← (PV_CurrentScaleInstall.selected ops).op61 tag
    (PV_CurrentScaleInstall.selected ops).op66 c)=_
  rw [PV_RW_CompressLiftSelectors.complex]
  simp only [bind_tc_ok,PV_RW_CompressLiftSelectors.quartic]
  rfl

def compress (ops : ExternalFuns) (tag : U32) (values : Slice U32)
    (lambda : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
  let out ← @logup.lift _ (PV_CurrentScaleInstall.selected ops) tag
  let iterator ← SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter values
  @ProverRw18InlineContext.run _ (PV_CurrentScaleInstall.selected ops) lambda iterator out lambda

theorem context (ops : ExternalFuns) (tag : U32) (values : Slice U32) (lambda : aspis_core.field.QM31) :
    compress ops tag values lambda=
      @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops) tag values lambda := by
  unfold compress logup.lift ProverRw18ContextCompression.compress
  simp only [bind_assoc_eq]

theorem owned (ops : ExternalFuns) (tag : U32) (values : Slice U32) (lambda : aspis_core.field.QM31) :
    compress ops tag values lambda=PV_RW_CompressClosed.owned tag values lambda :=
  (context ops tag values lambda).trans (ProverRw18ContextCompression.owned ops tag values lambda)

#print axioms initial
#print axioms context
#print axioms owned
end R1Z.ProverRw18OriginalLift
