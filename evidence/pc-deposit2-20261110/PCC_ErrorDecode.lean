import PCC_ProgramError
set_option autoImplicit false
namespace PCC
/-- Pinned SDK From<u64>; unknown high status values are truncated to Custom u32. -/
def ProgramError.fromStatus (status : UInt64) : ProgramError :=
  match status with
  | 4294967296 => .Custom (.ofNat 0)
  | 8589934592 => .InvalidArgument
  | 12884901888 => .InvalidInstructionData
  | 17179869184 => .InvalidAccountData
  | 21474836480 => .AccountDataTooSmall
  | 25769803776 => .InsufficientFunds
  | 30064771072 => .IncorrectProgramId
  | 34359738368 => .MissingRequiredSignature
  | 38654705664 => .AccountAlreadyInitialized
  | 42949672960 => .UninitializedAccount
  | 47244640256 => .NotEnoughAccountKeys
  | 51539607552 => .AccountBorrowFailed
  | 55834574848 => .MaxSeedLengthExceeded
  | 60129542144 => .InvalidSeeds
  | 64424509440 => .BorshIoError "Unknown"
  | 68719476736 => .AccountNotRentExempt
  | 73014444032 => .UnsupportedSysvar
  | 77309411328 => .IllegalOwner
  | 81604378624 => .MaxAccountsDataAllocationsExceeded
  | 85899345920 => .InvalidRealloc
  | 90194313216 => .MaxInstructionTraceLengthExceeded
  | 94489280512 => .BuiltinProgramsMustConsumeComputeUnits
  | 98784247808 => .InvalidAccountOwner
  | 103079215104 => .ArithmeticOverflow
  | 107374182400 => .Immutable
  | 111669149696 => .IncorrectAuthority
  | other => .Custom (UInt32.ofNat other.toNat)

def syscallReply (status : UInt64) : Except ProgramError Unit :=
  if status = 0 then .ok () else .error (ProgramError.fromStatus status)

theorem syscall_zero : syscallReply 0 = .ok () := rfl
theorem syscall_nonzero (s : UInt64) (h : s ≠ 0) :
    syscallReply s = .error (ProgramError.fromStatus s) := by
  simp only [syscallReply, if_neg h]
#print axioms syscall_zero
#print axioms syscall_nonzero
end PCC
