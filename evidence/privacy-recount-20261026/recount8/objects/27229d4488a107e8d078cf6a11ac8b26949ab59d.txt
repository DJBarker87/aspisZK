import R1Z.PV_RunJoin_PublicAgreement32
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_HonestReservation32
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_HonestIdentification26
local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
variable (base : ExternalTypes) (a b : Honest (K := K))
    (same : source_honest.public a=source_honest.public b)
    (header : PV_RunJoin_PublicAgreement32.header a.val=PV_RunJoin_PublicAgreement32.header b.val)
    (pool : a.val.snapshot.pool=b.val.snapshot.pool)
    (domain : a.val.snapshot.deployment_domain=b.val.snapshot.deployment_domain)

include base same header pool domain

theorem full_public : PV_Src_NativeInput.publicInput a.val=PV_Src_NativeInput.publicInput b.val := by
  have h := congrArg (PV_RunJoin_NativePublicInverse32.unPublic base)
    (PV_RunJoin_PublicAgreement32.honest base a b same header pool domain)
  simpa only [PV_RunJoin_NativePublicInverse32.from_input_roundtrip] using h
#print axioms full_public

/-- Complete native public-byte encoding Result, including errors and divergence,
 agrees under the derived full public equality. -/
theorem public_bytes (ops : @ExternalFuns (PDict_CodecDictionary.native base)) :
    letI : ExternalTypes := PDict_CodecDictionary.native base
    letI : ExternalFuns := PDict_CodecDictionary.selected base ops
    aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (PV_RunJoin_NominalPublicData.fromInput base a.val) =
    aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (PV_RunJoin_NominalPublicData.fromInput base b.val) := by
  letI : ExternalTypes := PDict_CodecDictionary.native base
  letI : ExternalFuns := PDict_CodecDictionary.selected base ops
  rw [PV_RunJoin_PublicAgreement32.honest base a b same header pool domain]
#print axioms public_bytes
end R1Z.PV_RunJoin_HonestReservation32
