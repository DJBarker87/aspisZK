import XRy_WholeDriver
import XRs_ClosedCallbacks
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport XRo_Join_ResultPair
set_option autoImplicit false
noncomputable section
namespace XRy_QueryLaws
abbrev CQE := AspisR1PublicPreparation.aspis_core.transcript.QuerySampleError
abbrev RQE := XRn_Join_Release.aspis_core.transcript.QuerySampleError

def qe : RQE → CQE
 | .BoundNotPowerOfTwo b => .BoundNotPowerOfTwo b
 | .CountExceedsBound n b => .CountExceedsBound n b
 | .DrawLimitExhausted n m => .DrawLimitExhausted n m

def rawBoundaries : AspisR1PublicPreparation.QueriesModel.Boundaries where
 decode := fun blocks advances => mapR (inner id qe)
   (XRn_Join_Release.aspis_core.r0_transcript.queries_from_pairs blocks advances)
 embed := aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31

theorem decode (blocks advances : XRv_QueryDriver.Blocks) :
 rawBoundaries.decode blocks advances =
 Query31ConcreteMaterializedSchedule.actualConcreteDecode
   Query31ConcreteDriverTraceFacts.sourceDefaultState blocks advances := by
 unfold rawBoundaries Query31ConcreteMaterializedSchedule.actualConcreteDecode
 rw [←XRy_WholeDriver.whole]
 cases XRn_Join_Release.aspis_core.r0_transcript.queries_from_pairs blocks advances with
 | ok r => cases r <;> rfl
 | fail e => rfl
 | div => rfl

#print axioms decode
#print aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
#print AspisS1M31Embedding.source_from_m31
#print AspisS1M31Embedding.Total.toPrep
#print AspisS1M31Embedding.Total.embed
end XRy_QueryLaws
