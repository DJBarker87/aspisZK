import R1Z.PV_RunJoin_PrepareOperations47
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareMaterialContext47
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Material := weights.Weights → W → Result (core.result.Result (alloc.vec.Vec W) verifier.Error)

theorem complete (variant : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (coefficients : Result (alloc.vec.Vec (Array W 1024#usize)))
    (request : Result Unit) (w : weights.Weights) (m1 m2 : Material)
    (hm : ∀ x, m1 w x=m2 w x) :
    PV_RunJoin_PrepareOperations47.run variant hash backend sem coefficients
        (do let _ ← request;ok (.Ok w)) m1=
      PV_RunJoin_PrepareOperations47.run variant hash backend sem coefficients
        (do let _ ← request;ok (.Ok w)) m2 := by
  cases request with
  | fail e => simp only [PV_RunJoin_PrepareOperations47.run,bind_tc_fail]
  | div => simp only [PV_RunJoin_PrepareOperations47.run,bind_tc_div]
  | ok u =>
    simp only [PV_RunJoin_PrepareOperations47.run,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch,hm]
#print axioms complete
end R1Z.PV_RunJoin_PrepareMaterialContext47
