import NIS_EntryPrefixes
set_option autoImplicit false
namespace AspisR1.NIV_ReplyCuts
open Aeneas Aeneas.Std Result
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev PR := core.result.Result Unit PE

/-- NIV_forward.rs, assertion `result==expected`. This cut records ONLY the
return assertion. It has no input-descriptor, heap, cleanup or endpoint fact.
The packet hash and exact native fixture domain are in NIV_CERTIFICATES.md.
It is not an admitted complete (ak) forwarding cut. -/
def replyCut (returned logged : PR) : Prop := returned = logged

/-- The complete nominal error carrier includes the string payload. Native
NIV forwarding probes cover only the literal string "NIV" in that arm. -/
def errorTag : PE → Nat
  | .Custom _ => 1 | .InvalidArgument => 2 | .InvalidInstructionData => 3
  | .InvalidAccountData => 4 | .AccountDataTooSmall => 5 | .InsufficientFunds => 6
  | .IncorrectProgramId => 7 | .MissingRequiredSignature => 8
  | .AccountAlreadyInitialized => 9 | .UninitializedAccount => 10
  | .NotEnoughAccountKeys => 11 | .AccountBorrowFailed => 12
  | .MaxSeedLengthExceeded => 13 | .InvalidSeeds => 14
  | .AccountNotRentExempt => 15 | .UnsupportedSysvar => 16 | .IllegalOwner => 17
  | .MaxAccountsDataAllocationsExceeded => 18 | .InvalidRealloc => 19
  | .MaxInstructionTraceLengthExceeded => 20 | .BuiltinProgramsMustConsumeComputeUnits => 21
  | .InvalidAccountOwner => 22 | .ArithmeticOverflow => 23 | .Immutable => 24
  | .IncorrectAuthority => 25 | .BorshIoError _ => 26

def tag : PR → Nat
  | .Ok _ => 0
  | .Err e => errorTag e

theorem errorTag_bound (e : PE) : 1 ≤ errorTag e ∧ errorTag e ≤ 26 := by
  cases e <;> simp only [errorTag] <;> omega

theorem tag_bound (r : PR) : tag r ≤ 26 := by
  cases r with
  | Ok u => exact Nat.zero_le _
  | Err e => exact (errorTag_bound e).2

/-- No error payload is erased by a native reply cut, including the complete
Borsh string. This is conditional on the cut; it does not extend its domain. -/
theorem payload (returned : PR) (e : PE)
    (cut : replyCut returned (.Err e)) : returned = .Err e := cut

theorem success (returned : PR)
    (cut : replyCut returned (.Ok ())) : returned = .Ok () := cut

theorem tags (returned logged : PR) (cut : replyCut returned logged) :
    tag returned = tag logged := congrArg tag cut

/-- The model's full returning carrier has the selected child's exact reply.
This theorem supplies the model side only: it does not establish native
input-descriptor/SDK producer association missing from the probes. -/
theorem selected_first {Account State Event : Type}
    (children : NGL_EntryRouting.Children Account State Event)
    (id : NGL_EntryRouting.Key) (accounts : Slice Account) (data : Slice U8) (state : State)
    (selected : Hiq_ReleaseRoute.route data = .first) :
    (NGL_EntryRouting.run children id accounts data state).1.result =
      (children.first id accounts data state).result := by
  rw [NIS_EntryPrefixes.first_forward children id accounts data state selected]

theorem selected_second {Account State Event : Type}
    (children : NGL_EntryRouting.Children Account State Event)
    (id : NGL_EntryRouting.Key) (accounts : Slice Account) (data : Slice U8) (state : State)
    (selected : Hiq_ReleaseRoute.route data = .second) :
    (NGL_EntryRouting.run children id accounts data state).1.result =
      (children.second id accounts data state).result := by
  rw [NIS_EntryPrefixes.second_forward children id accounts data state selected]

#print axioms errorTag_bound
#print axioms tag_bound
#print axioms payload
#print axioms success
#print axioms tags
#print axioms selected_first
#print axioms selected_second
end AspisR1.NIV_ReplyCuts
