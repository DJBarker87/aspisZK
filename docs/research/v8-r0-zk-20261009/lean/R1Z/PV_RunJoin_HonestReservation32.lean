import R1Z.PV_RunJoin_PublicAgreement32
import R1Z.PV_RunJoin_NativePublicReservation
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

theorem public : PV_Src_NativeInput.publicInput a.val=PV_Src_NativeInput.publicInput b.val := by
  have h := congrArg (PV_RunJoin_NativePublicInverse32.unPublic base)
    (PV_RunJoin_PublicAgreement32.honest base a b same header pool domain)
  simpa only [PV_RunJoin_NativePublicInverse32.from_input_roundtrip] using h
#print axioms public

/-- The COMPLETE reservation prefix Result agrees on the common nonce,
including failure and divergence. No entropy success or compiler-trace equality
is required; this does not assert equality of the remaining prover body. -/
theorem prefix (ops : @ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (address : PV_RunJoin_LedgerWorld.Address) (nonce : Array U8 32#usize) :
    letI : ExternalTypes := PDict_CodecDictionary.native base
    letI : ExternalFuns := PDict_CodecDictionary.selected base ops
    PV_RunJoin_PublicReservation.entry address (PV_RunJoin_NominalPublicData.fromInput base a.val) .S2 hash nonce =
    PV_RunJoin_PublicReservation.entry address (PV_RunJoin_NominalPublicData.fromInput base b.val) .S2 hash nonce := by
  letI : ExternalTypes := PDict_CodecDictionary.native base
  letI : ExternalFuns := PDict_CodecDictionary.selected base ops
  exact PV_RunJoin_PublicReservation.common address _ _ .S2 hash hash nonce nonce
    (PV_RunJoin_PublicAgreement32.honest base a b same header pool domain) rfl rfl
#print axioms prefix
end R1Z.PV_RunJoin_HonestReservation32
