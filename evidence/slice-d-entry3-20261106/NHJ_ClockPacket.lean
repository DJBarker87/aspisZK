import S2W_ExtractionBoundary
set_option autoImplicit false
namespace NHJ_ClockPacket
open Aeneas Aeneas.Std Result
abbrev PE := AdapterRw.solana_program_error.ProgramError
/-- The SDK field carrier for the caller's after-get continuation only.
This does not extract or implement Clock::get or adopt a syscall law. -/
structure Fields where
  slot : U64
  epochStart : I64
  epoch : U64
  leaderScheduleEpoch : U64
  unixTimestamp : I64

def project : core.result.Result Fields PE → AspisR1.S2W_ExtractionBoundary.Slot
  | .Ok clock => .Ok clock.slot
  | .Err error => .Err error

theorem success (clock : Fields) : project (.Ok clock) = .Ok clock.slot := rfl

theorem error_payload (error : PE) : project (.Err error) = .Err error := rfl

theorem unused_fields (slot epoch leader : U64) (start time : I64) :
    project (.Ok ⟨slot,start,epoch,leader,time⟩) = .Ok slot := rfl
#print axioms success
#print axioms error_payload
#print axioms unused_fields
end NHJ_ClockPacket
