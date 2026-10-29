import R1Z.PV_RunJoin_PreparedDomain48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareTail48
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev W := aspis_core.field.wide_exact.WideExact

def run (variant : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (transcript2 : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
    (y1 : alloc.vec.Vec U8) (gamma inactive kappa : W) (q w : Slice W) :
    Result (core.result.Result prover.PreparedOpening verifier.Error) := do
  let s6 := q
  let s7 := w
  let c0 ← prover.round s6 s7
  let s8 ← Aeneas.Std.lift (Array.to_slice c0)
  let c0bytes ← prover.encoded_slice s8
  let s9 := alloc.vec.Vec.deref c0bytes
  let (alpha0, transcript3) ←
    host_transcript.Transcript.scalar
      aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
      transcript2 29#u8 s9 false
  let s10 := q
  let q1 ← prover.fold s10 alpha0 false
  let s11 := w
  let w1 ← prover.fold s11 alpha0 true
  let s12 := alloc.vec.Vec.deref q1
  PV_RunJoin_PreparedDomain48.run backend sem transcript3 y1 gamma inactive kappa alpha0
    c0bytes q1 w1 (
    host_commitment.EncodingDomain.evaluate
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField
      backend.domain s12 0#usize)
#print axioms run
end R1Z.PV_RunJoin_PrepareTail48
