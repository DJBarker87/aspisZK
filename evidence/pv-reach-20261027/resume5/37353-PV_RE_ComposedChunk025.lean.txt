import R1Z.PV_RE_ComposedContextsGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix025
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_sumcheck.prove_sumcheck`.
Recursive calls remain the original extracted calls. -/
def continueAfter {H : Type} {T1 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle T1) (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec Std.U8) (initial_claim : aspis_core.field.QM31) (oracle : T1) (out : Payload (aspis_core.field.QM31.ZERO)) : Result ((core.result.Result ((Array aspis_core.field.QM31 10#usize) ×
    aspis_core.field.QM31) r1_wire.Error) × (host_wire.SemanticTranscript H)
    × (alloc.vec.Vec Std.U8)) := do
  let q := out
  let a := Array.repeat 10#usize q
  host_sumcheck.prove_sumcheck_rounds aspis_coredigestDigest32Inst OracleInst
    transcript output a initial_claim 0#usize oracle


end R1Z.PV_RE_ComposedSuffix025
pv_composed_source_contexts ProverRwFull.host_sumcheck.prove_sumcheck
pv_composed_source_contexts R1Z.PV_RE_ComposedSuffix025.continueAfter
