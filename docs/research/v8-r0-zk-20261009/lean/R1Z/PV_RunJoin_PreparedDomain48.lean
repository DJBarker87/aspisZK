import R1Z.PV_RunJoin_PrepareOperations47
import R1Z.PV_RunJoin_OpeningResult48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PreparedDomain48
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Domain := Result (core.result.Result (alloc.vec.Vec W) aspis_core.r0.Error)

def run (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (transcript : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
    (y1 : alloc.vec.Vec U8) (gamma inactive kappa alpha0 : W) (c0bytes : alloc.vec.Vec U8)
    (q1 w1 : alloc.vec.Vec W) (domain : Domain) : Result (core.result.Result prover.PreparedOpening verifier.Error) := do
  let r2 ← domain
  let r3 ← core.result.Result.map_err
    prover.prepare_opening.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError r2 ()
  let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
  match cf2 with
  | .Continue val2 => ok (.Ok {backend,sem,transcript,y1,gamma,inactive,kappa,alpha0,c0bytes,q1,w1,folded_word:=val2})
  | .Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      prover.PreparedOpening (core.convert.FromSame verifier.Error) residual

theorem success (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (transcript : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
    (y1 : alloc.vec.Vec U8) (gamma inactive kappa alpha0 : W) (c0bytes : alloc.vec.Vec U8)
    (q1 w1 folded : alloc.vec.Vec W) :
    run backend sem transcript y1 gamma inactive kappa alpha0 c0bytes q1 w1 (ok (.Ok folded))=
      ok (.Ok {backend,sem,transcript,y1,gamma,inactive,kappa,alpha0,c0bytes,q1,w1,folded_word:=folded}) := rfl

theorem inner_error (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (transcript : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
    (y1 : alloc.vec.Vec U8) (gamma inactive kappa alpha0 : W) (c0bytes : alloc.vec.Vec U8)
    (q1 w1 : alloc.vec.Vec W) (e : aspis_core.r0.Error) :
    run backend sem transcript y1 gamma inactive kappa alpha0 c0bytes q1 w1 (ok (.Err e))=
      ok (.Err verifier.Error.Allocation) := rfl

theorem failure (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (transcript : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
    (y1 : alloc.vec.Vec U8) (gamma inactive kappa alpha0 : W) (c0bytes : alloc.vec.Vec U8)
    (q1 w1 : alloc.vec.Vec W) (e : Error) :
    run backend sem transcript y1 gamma inactive kappa alpha0 c0bytes q1 w1 (fail e)=fail e := rfl

theorem divergence (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (transcript : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
    (y1 : alloc.vec.Vec U8) (gamma inactive kappa alpha0 : W) (c0bytes : alloc.vec.Vec U8)
    (q1 w1 : alloc.vec.Vec W) :
    run backend sem transcript y1 gamma inactive kappa alpha0 c0bytes q1 w1 div=div := rfl
#print axioms success
#print axioms inner_error
#print axioms failure
#print axioms divergence
end R1Z.PV_RunJoin_PreparedDomain48
