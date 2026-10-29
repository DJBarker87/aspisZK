import R1Z.PV_RunJoin_PrepareOperations47
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareVariant48
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev W := aspis_core.field.wide_exact.WideExact

theorem complete (variant : transport.Variant) (h : variant≠.S2)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (coefficients : Result (alloc.vec.Vec (Array W 1024#usize)))
    (constructor : Result (core.result.Result weights.Weights verifier.Error))
    (materialize : weights.Weights → W → Result (core.result.Result (alloc.vec.Vec W) verifier.Error)) :
    PV_RunJoin_PrepareOperations47.run variant hash backend sem coefficients constructor materialize=
      ok (.Err verifier.Error.Semantic) := by
  cases variant with
  | D => rfl
  | S1 => rfl
  | S2 => exact False.elim (h rfl)
#print axioms complete
end R1Z.PV_RunJoin_PrepareVariant48
