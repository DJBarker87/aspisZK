import R1Z.PV_RunJoin_HonestReservation32
import R1Z.PV_RunJoin_NativePublicReservation
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_HonestLedger32
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_HonestIdentification26
local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
variable {N C : Type}
variable (base : ExternalTypes) (a b : Honest (K := K))
    (same : source_honest.public a=source_honest.public b)
    (header : PV_RunJoin_PublicAgreement32.header a.val=PV_RunJoin_PublicAgreement32.header b.val)
    (pool : a.val.snapshot.pool=b.val.snapshot.pool)
    (domain : a.val.snapshot.deployment_domain=b.val.snapshot.deployment_domain)
include same header pool domain

/-- Complete prefix result, before any private compiled columns are consumed. -/
theorem prefix_result (ops : @ExternalFuns (PDict_CodecDictionary.native base))
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
#print axioms prefix_result

/-- On a common source world and common secret, both actually returned ledger
models agree even when the private compiled payloads differ. No equality of
native filesystem events or complete proof/observer results is inferred. -/
theorem ledger
    (ops : PV_RunJoin_NativeSelectedInputs.LedgerState base N C → @ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (schedule : ProverCommitLedger36.Schedule) (unix : Bool) (address : PV_RunJoin_LedgerWorld.Address)
    (secret : ProverRwRetryModel.Secret)
    (s left right : PV_RunJoin_NativeSelectedInputs.LedgerState base N C)
    (leftStatus rightStatus : core.result.Result ProverRwRetryModel.Proof verifier.Error)
    (run_left : letI : ExternalTypes := PDict_CodecDictionary.native base
      PV_RunJoin_LedgerBody.body schedule unix address
        (PV_RunJoin_NativeSelectedInputs.ledgerInputs base ops hash a.val) secret s = .ok (leftStatus,left))
    (run_right : letI : ExternalTypes := PDict_CodecDictionary.native base
      PV_RunJoin_LedgerBody.body schedule unix address
        (PV_RunJoin_NativeSelectedInputs.ledgerInputs base ops hash b.val) secret s = .ok (rightStatus,right)) :
    letI : ExternalTypes := PDict_CodecDictionary.native base
    left.ledger.model=right.ledger.model := by
  letI : ExternalTypes := PDict_CodecDictionary.native base
  exact PV_RunJoin_NativePublicReservation.ledger_eq base ops hash schedule unix address a.val b.val secret
    s left right leftStatus rightStatus
    (PV_RunJoin_HonestReservation32.full_public base a b same header pool domain) run_left run_right
#print axioms ledger
end R1Z.PV_RunJoin_HonestLedger32
