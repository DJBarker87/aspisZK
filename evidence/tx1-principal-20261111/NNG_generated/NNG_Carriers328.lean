import NNG_Candidate094
import NMT_345First_T5
import NMT_345Prep_T5
import NMT_first.Funs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Carriers328
open Aeneas Aeneas.Std Result
abbrev Public := NMT_first.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Error := NMT_first.aspis_r1_cost_probe.verifier.Error

def toPublic (p : Public) : LIB_VCarriers.Public := NMT_345Prep.toT5 (NMT_345First.fromT5 p)
def fromPublic (p : LIB_VCarriers.Public) : Public := NMT_345First.toT5 (NMT_345Prep.fromT5 p)
theorem to_from (p : LIB_VCarriers.Public) : toPublic (fromPublic p)=p := by
 unfold toPublic fromPublic
 rw [NMT_345First.toT5_inverse,NMT_345Prep.fromT5_inverse]
#print axioms to_from
theorem from_to (p : Public) : fromPublic (toPublic p)=p := by
 unfold toPublic fromPublic
 rw [NMT_345Prep.toT5_inverse,NMT_345First.fromT5_inverse]
#print axioms from_to

def error : Error → LIB_VCarriers.VErr
 | .Parse=>.Parse | .Semantic=>.Semantic | .Transcript=>.Transcript | .Relation=>.Relation
 | .Merkle=>.Merkle | .Query=>.Query | .Checkpoint=>.Checkpoint | .Allocation=>.Allocation
def errorBack : LIB_VCarriers.VErr → Error
 | .Parse=>.Parse | .Semantic=>.Semantic | .Transcript=>.Transcript | .Relation=>.Relation
 | .Merkle=>.Merkle | .Query=>.Query | .Checkpoint=>.Checkpoint | .Allocation=>.Allocation
theorem error_back (e : LIB_VCarriers.VErr) : error (errorBack e)=e := by cases e <;> rfl
#print axioms error_back
-- ProgramError transport follows NMT_345RSLCarriers.pe; all payloads retained.
def pe : NMT_first.solana_program_error.ProgramError → RSL.ProgramError
 | .Custom x => .custom (UInt32.ofNat x.val)
 | .InvalidArgument => .invalidArgument
 | .InvalidInstructionData => .invalidInstructionData
 | .InvalidAccountData => .invalidAccountData
 | .AccountDataTooSmall => .accountDataTooSmall
 | .InsufficientFunds => .insufficientFunds
 | .IncorrectProgramId => .incorrectProgramId
 | .MissingRequiredSignature => .missingRequiredSignature
 | .AccountAlreadyInitialized => .accountAlreadyInitialized
 | .UninitializedAccount => .uninitializedAccount
 | .NotEnoughAccountKeys => .notEnoughAccountKeys
 | .AccountBorrowFailed => .accountBorrowFailed
 | .MaxSeedLengthExceeded => .maxSeedLengthExceeded
 | .InvalidSeeds => .invalidSeeds
 | .BorshIoError x => .borshIoError x
 | .AccountNotRentExempt => .accountNotRentExempt
 | .UnsupportedSysvar => .unsupportedSysvar
 | .IllegalOwner => .illegalOwner
 | .MaxAccountsDataAllocationsExceeded => .maxAccountsDataAllocationsExceeded
 | .InvalidRealloc => .invalidRealloc
 | .MaxInstructionTraceLengthExceeded => .maxInstructionTraceLengthExceeded
 | .BuiltinProgramsMustConsumeComputeUnits => .builtinProgramsMustConsumeComputeUnits
 | .InvalidAccountOwner => .invalidAccountOwner
 | .ArithmeticOverflow => .arithmeticOverflow
 | .Immutable => .immutable
 | .IncorrectAuthority => .incorrectAuthority

def childReply : NNG_Context094.Output → core.result.Result (alloc.vec.Vec U8) Error
 | .Ok b=>.Ok b | .Err e=>.Err (errorBack (NNG_ParseCall094.error e))
def childPort : core.result.Result (alloc.vec.Vec U8) Error → Except LIB_VCarriers.VErr RSL.Bytes
 | .Ok b=>.ok (LIB_Carriers.bytes b.deref) | .Err e=>.error (error e)
def port : core.result.Result (alloc.vec.Vec U8) NMT_first.solana_program_error.ProgramError → Except RSL.ProgramError RSL.Bytes
 | .Ok b=>.ok (LIB_Carriers.bytes b.deref) | .Err e=>.error (pe e)
theorem child_reply (r : NNG_Context094.Output) : childPort (childReply r)=NNG_ProducerFull094.port r := by
 cases r with
 | Ok b=>rfl
 | Err e=>exact congrArg Except.error (error_back _)
#print axioms child_reply
end AspisR1.NNG_Carriers328
