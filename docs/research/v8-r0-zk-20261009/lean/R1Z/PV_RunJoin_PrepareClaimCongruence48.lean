import R1Z.PV_RunJoin_PrepareClaimContext48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareClaimCongruence48
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Column := Array W 1024#usize
abbrev Point := aspis_core.r0.domain.Point W
abbrev Claim := Slice Column → Point → Result (alloc.vec.Vec U8)
abbrev Inactive := Slice W → weights.Weights → Result W
abbrev Material := weights.Weights → W → Result (core.result.Result (alloc.vec.Vec W) verifier.Error)

theorem claim (variant : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (coefficients : alloc.vec.Vec Column)
    (constructor : Result (core.result.Result weights.Weights verifier.Error))
    (material : Material) (c1 c2 : Claim) (inactive : Inactive)
    (hc : ∀ point,c1 (alloc.vec.Vec.deref coefficients) point=c2 (alloc.vec.Vec.deref coefficients) point) :
    PV_RunJoin_PrepareClaimContext48.run variant hash backend sem (ok coefficients) constructor material c1 inactive=
      PV_RunJoin_PrepareClaimContext48.run variant hash backend sem (ok coefficients) constructor material c2 inactive := by
  simp only [PV_RunJoin_PrepareClaimContext48.run,bind_tc_ok,hc]

theorem inactive (variant : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (coefficients : Result (alloc.vec.Vec Column)) (request : Result Unit) (w : weights.Weights)
    (material : Material) (c : Claim) (i1 i2 : Inactive) (hi : ∀ q,i1 q w=i2 q w) :
    PV_RunJoin_PrepareClaimContext48.run variant hash backend sem coefficients
      (do let _ ← request;ok (.Ok w)) material c i1=
      PV_RunJoin_PrepareClaimContext48.run variant hash backend sem coefficients
        (do let _ ← request;ok (.Ok w)) material c i2 := by
  cases request with
  | fail e => simp only [PV_RunJoin_PrepareClaimContext48.run,bind_tc_fail]
  | div => simp only [PV_RunJoin_PrepareClaimContext48.run,bind_tc_div]
  | ok u =>
    simp only [PV_RunJoin_PrepareClaimContext48.run,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch,hi]
#print axioms claim
#print axioms inactive
end R1Z.PV_RunJoin_PrepareClaimCongruence48
