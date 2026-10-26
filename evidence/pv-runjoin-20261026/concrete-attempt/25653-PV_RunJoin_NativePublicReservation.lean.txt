import R1Z.PV_RunJoin_NativeSelectedInputs
import R1Z.PV_RunJoin_LedgerPublicShape
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativePublicReservation
open Aeneas Aeneas.Std Result ProverRwFull
local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable {N C : Type}

theorem public_eq (base : ExternalTypes) (a b : PV_Src_NativeInput.Input)
    (same : PV_Src_NativeInput.publicInput a = PV_Src_NativeInput.publicInput b) :
    PV_RunJoin_NominalPublicData.fromInput base a = PV_RunJoin_NominalPublicData.fromInput base b := by
  rw [PV_RunJoin_NominalPublicData.selected_public,PV_RunJoin_NominalPublicData.selected_public,same]

theorem decision_eq (base : ExternalTypes)
    (ops : PV_RunJoin_NativeSelectedInputs.LedgerState base N C → @ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (address : PV_RunJoin_LedgerWorld.Address) (a b : PV_Src_NativeInput.Input)
    (nonce nonce' : Array U8 32#usize) (s : PV_RunJoin_NativeSelectedInputs.LedgerState base N C)
    (same_public : PV_Src_NativeInput.publicInput a = PV_Src_NativeInput.publicInput b)
    (same_nonce : nonce = nonce') :
    letI : ExternalTypes := PDict_CodecDictionary.native base
    PV_RunJoin_PublicDecision.decision (PDict_CodecDictionary.selected base (ops s))
      address (PV_RunJoin_NominalPublicData.fromInput base a) .S2 hash nonce =
    PV_RunJoin_PublicDecision.decision (PDict_CodecDictionary.selected base (ops s))
      address (PV_RunJoin_NominalPublicData.fromInput base b) .S2 hash nonce' := by
  letI : ExternalTypes := PDict_CodecDictionary.native base
  exact PV_RunJoin_PublicDecision.common _ address _ _ .S2 hash hash nonce nonce'
    (public_eq base a b same_public) rfl same_nonce

/-- Pure source ledger consequence at the real selected input interface.
The two compilations may differ completely. Actual filesystem trace/E2 and
complete observer decoding are separate obligations. -/
theorem ledger_eq (base : ExternalTypes)
    (ops : PV_RunJoin_NativeSelectedInputs.LedgerState base N C → @ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (schedule : ProverCommitLedger36.Schedule) (unix : Bool) (address : PV_RunJoin_LedgerWorld.Address)
    (a b : PV_Src_NativeInput.Input)
    (secret : ProverRwRetryModel.Secret)
    (s left right : PV_RunJoin_NativeSelectedInputs.LedgerState base N C)
    (leftStatus rightStatus : core.result.Result ProverRwRetryModel.Proof verifier.Error)
    (same_public : PV_Src_NativeInput.publicInput a = PV_Src_NativeInput.publicInput b)
    (run_left : letI : ExternalTypes := PDict_CodecDictionary.native base
      PV_RunJoin_LedgerBody.body schedule unix address
        (PV_RunJoin_NativeSelectedInputs.ledgerInputs base ops hash a) secret s = .ok (leftStatus,left))
    (run_right : letI : ExternalTypes := PDict_CodecDictionary.native base
      PV_RunJoin_LedgerBody.body schedule unix address
        (PV_RunJoin_NativeSelectedInputs.ledgerInputs base ops hash b) secret s = .ok (rightStatus,right)) :
    letI : ExternalTypes := PDict_CodecDictionary.native base
    left.ledger.model = right.ledger.model := by
  letI : ExternalTypes := PDict_CodecDictionary.native base
  have l := PV_RunJoin_LedgerPublicShape.ledger_public schedule unix address
    (PV_RunJoin_NativeSelectedInputs.ledgerInputs base ops hash a) secret s left leftStatus run_left
  have r := PV_RunJoin_LedgerPublicShape.ledger_public schedule unix address
    (PV_RunJoin_NativeSelectedInputs.ledgerInputs base ops hash b) secret s right rightStatus run_right
  have same := decision_eq base ops hash address a b secret.mask_nonce secret.mask_nonce s same_public rfl
  change left.ledger.model = _ at l
  change right.ledger.model = _ at r
  dsimp only [PV_RunJoin_NativeSelectedInputs.ledgerInputs] at l r
  rw [same] at l
  exact l.trans r.symm

#print axioms public_eq
#print axioms decision_eq
#print axioms ledger_eq
end R1Z.PV_RunJoin_NativePublicReservation
