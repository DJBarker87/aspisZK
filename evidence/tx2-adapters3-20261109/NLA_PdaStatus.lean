import NKF_PdaModel
set_option autoImplicit false
noncomputable section
namespace NLA_PdaStatus
open Aeneas Aeneas.Std Result
abbrev Key := NKF_PdaModel.Key
abbrev PdaError := NKF_PdaModel.PdaError
/-- Reviewed SDK status transcription, source a667b28c... . This is a local
status law, not a syscall ABI certificate or a PDA-value assumption. -/
def reply (panic : Error) (status : U64) (output : Key) :
 Result (core.result.Result Key PdaError) :=
 if status.val = 0 then ok (.Ok output)
 else if status.val = 1 then ok (.Err .InvalidSeeds)
 else if status.val = 2 then ok (.Err .IllegalOwner)
 else .fail panic

theorem success (panic : Error) (output : Key) :
 reply panic 0#u64 output = ok (.Ok output) := rfl

theorem invalid_seeds (panic : Error) (output : Key) :
 reply panic 1#u64 output = ok (.Err .InvalidSeeds) := rfl

theorem illegal_owner (panic : Error) (output : Key) :
 reply panic 2#u64 output = ok (.Err .IllegalOwner) := rfl

theorem unsupported (panic : Error) (status : U64) (output : Key)
 (large : 2 < status.val) : reply panic status output = .fail panic := by
 have h0 : status.val ≠ 0 := by omega
 have h1 : status.val ≠ 1 := by omega
 have h2 : status.val ≠ 2 := by omega
 simp only [reply,if_neg h0,if_neg h1,if_neg h2]

/-- Unsupported statuses do not become mapped InvalidAccountData returns.
The SDK panics before map_err or the caller comparison can execute. -/
theorem unsupported_prefix (panic : Error) (status : U64) (output : Key)
 (large : 2 < status.val) :
 NKF_PdaModel.continuation (reply panic status output) = .fail panic := by
 rw [unsupported panic status output large]
 rfl

#print axioms success
#print axioms invalid_seeds
#print axioms illegal_owner
#print axioms unsupported
#print axioms unsupported_prefix
end NLA_PdaStatus
