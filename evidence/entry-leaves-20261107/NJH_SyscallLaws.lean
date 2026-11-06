import NJH_Ref.Funs
set_option autoImplicit false
namespace NJH_SyscallLaws
open Aeneas Aeneas.Std Result
/-- Complete Clock value carrier, including both signed timestamps. The
status-to-ProgramError conversion and actual syscall association remain separate. -/
theorem clock_ok (c : NJH_Ref.Clock) :
    NJH_Ref.clock_ref 0#u64 c = ok (.Ok c) := by
  rfl
theorem clock_error (status : U64) (c : NJH_Ref.Clock) (h : status ≠ 0#u64) :
    NJH_Ref.clock_ref status c = ok (.Err status) := by
  simp only [NJH_Ref.clock_ref, if_neg h]
/-- The syscall's reply bytes are preserved, with no assertion of a PDA value. -/
theorem pda_ok (bytes : Array U8 32#usize) :
    NJH_Ref.pda_reply_ref 0#u64 bytes = ok (.Ok bytes) := by
  rfl
theorem pda_error (status : U64) (bytes : Array U8 32#usize) (h : status ≠ 0#u64) :
    NJH_Ref.pda_reply_ref status bytes = ok (.Err status) := by
  simp only [NJH_Ref.pda_reply_ref, if_neg h]
theorem clock_frame {S E : Type} (status : U64) (c : NJH_Ref.Clock)
    (s : S) (events : List E) :
    (NJH_Ref.clock_ref status c,s,events) =
      ((if status = 0#u64 then ok (.Ok c) else ok (.Err status)),s,events) := rfl
#print axioms clock_ok
#print axioms clock_error
#print axioms pda_ok
#print axioms pda_error
#print axioms clock_frame
end NJH_SyscallLaws
