import NJG_RoundProducer
import NIX_CertificateFrames
set_option autoImplicit false
namespace AspisR1.NJG_RoundCode
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run)
abbrev Q := aspis_core.field.QM31
abbrev Alpha := Array Q 10#usize
abbrev Poly := Array Q 28#usize
abbrev Out (H : Type) := core.result.Result (Q × Alpha × r1_wire.SemanticTranscript H) r1_wire.Error

/-- Decoder-error stage. It has no semantic or value suffix. -/
def afterDecode {H : Type} (B : RoundModel.Boundaries) (D : aspis_core.Digest32 H)
 (record : r1_wire.ValidatedRecord) (t : r1_wire.SemanticTranscript H)
 (alpha : Alpha) (running : Q) (round : Usize)
 (decoded : core.result.Result Poly r1_wire.Error) : Code (Out H) := do
 let cf←core.result.Result.Insts.CoreOpsTry.branch decoded
 match cf with
 | .Break residual=>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    (Q × Alpha × r1_wire.SemanticTranscript H) (core.convert.FromSame r1_wire.Error) residual
 | .Continue polynomial=>
   let boundary←B.boundary polynomial
   let unequal←core.cmp.PartialEq.ne.trait_default aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 boundary running
   if unequal then pure (.Err (.Boundary round)) else
    let (semantic,post)←S1SemanticCode.semanticValidated D t record
    let cf←core.result.Result.Insts.CoreOpsTry.branch semantic
    match cf with
    | .Break residual=>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
       (Q × Alpha × r1_wire.SemanticTranscript H) (core.convert.FromSame r1_wire.Error) residual
    | .Continue challenge=>
      let updated←Array.update alpha round challenge
      let value←B.value polynomial updated round
      pure (.Ok (value,updated,post))

/-- Stage G after the original getter, with all source child calls retained. -/
def fromRecord {H : Type} (B : RoundModel.Boundaries) (D : aspis_core.Digest32 H)
 (record : r1_wire.ValidatedRecord) (t : r1_wire.SemanticTranscript H)
 (alpha : Alpha) (running : Q) (round : Usize) : Code (Out H) := do
 let decoded←B.decode 28#usize record 0#usize
 afterDecode B D record t alpha running round decoded

/-- Concrete producer packet supplies the row before every descendant call.
No result of a descendant, accepted finish or chosen execution is a premise. -/
theorem source {H : Type} (B : RoundModel.Boundaries) (D : aspis_core.Digest32 H)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix) (t : r1_wire.SemanticTranscript H)
 (alpha : Alpha) (running : Q) (round : Usize) (bound : round.val<10) :
 ∃ record,record.row=NJG_RoundProducer.row round bound ∧
 run (S1SemanticCode.roundStep B D (PrefixAdapter.fromOld pre) t alpha running round)=
 run (fromRecord B D record t alpha running round) := by
 obtain ⟨record,getter,tag,frame⟩:=NJG_RoundProducer.same_record pre round bound
 refine ⟨record,tag,?_⟩
 simp only [S1SemanticCode.roundStep,NGX_CodeTrace.lift_bind,lift,
  NJG_RoundProducer.row_add round bound,getter,bind_tc_ok,
  core.result.Result.Insts.CoreOpsTry.branch,fromRecord,afterDecode]

/-- Native decoder rejection never invokes later stage boundaries. -/
theorem rejected {H : Type} (B : RoundModel.Boundaries) (D : aspis_core.Digest32 H)
 (record : r1_wire.ValidatedRecord) (t : r1_wire.SemanticTranscript H)
 (alpha : Alpha) (running : Q) (round : Usize) (error : r1_wire.Error) :
 run (afterDecode B D record t alpha running round (.Err error))=([],ok (.Err error)) := rfl

#print axioms source
#print axioms rejected
end AspisR1.NJG_RoundCode
