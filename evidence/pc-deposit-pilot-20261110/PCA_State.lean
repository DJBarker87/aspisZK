import NLF_ProgramFold
import PCA_Errors
set_option autoImplicit false
namespace PCA
abbrev Bytes := List UInt8
abbrev Key := Vector UInt8 32
abbrev Digest := Vector UInt32 8
abbrev ProgramError := UInt64
inductive Outcome (α : Type) where
  | ok (value : α)
  | error (code : Failure)
  | abort (reason : String)
structure Meta where
  key : Key
  signer : Bool
  writable : Bool
structure Instruction where
  program : Key
  metas : List Meta
  data : Bytes
structure Invocation where
  instruction : Instruction
  infos : List Nat
  seeds : List (List Bytes)
structure CpiRecord where
  invocation : Invocation
  reply : Outcome Unit
structure Rent where
  lamportsPerByteYear : UInt64
  exemptionThresholdBits : UInt64
  burnPercent : UInt8
/-- ONE parent state. SDK account/cell identities and counters are carried by
loans, never reinstalled from entry admission after a child or CPI. Account
indices below accountCount are the admitted list, in source order. -/
structure PCA_State where
  programId : Key
  instructionData : Bytes
  rent : Rent
  accountCount : Nat
  loans : NLF_ParentModel.Parent
  liveGuards : List NLF_RefCell.Guard
  cpiHistory : List CpiRecord
  syscallHistory : List (String × List Bytes × Outcome Bytes)
  returned : Option (Outcome Unit)
structure Request where
  ownerKey : Digest
  amount : UInt32
  salt : Digest
  encryptedNotePayload : Bytes
structure Identity where
  pool : Key
  assetMint : Key
  tokenProgram : Key
  assetId : UInt32
  deploymentDomain : Key
structure Policy where
  flags : UInt8
  registryProgram : Key
  registryAuthority : Key
  policyBinding : Key
structure Master where
  bump : UInt8
  identity : Identity
  verifierPolicy : Policy
  initializedLaneMask : UInt8
  hasCheckpoint : Bool
  nextCheckpointSequence : UInt64
  lastCheckpointLaneSequences : Vector UInt64 8
structure Tree where
  nextLeafIndex : UInt64
  root : Digest
  frontier : Vector Digest 20
structure Lane where
  bump : UInt8
  master : Key
  laneId : UInt8
  tree : Tree
structure PairWitness where
  firstCommitment : Digest
  secondOccupied : UInt32
  secondCommitment : Digest
  secondOccupancyInverse : UInt32
structure Location where
  pageNumber : UInt64
  slot : UInt16
structure Append where
  leafIndex : UInt64
  rootSequence : UInt64
  root : Digest
  history : Location
structure Header where
  pool : Key
  pageNumber : UInt64
  firstSequence : UInt64
  filled : UInt16
inductive Preparation where | createOrAllocate | existingZeroed
  deriving DecidableEq
inductive Mode where
  | fresh (preparation : Preparation) (bump : UInt8)
  | same (header : Header)
  | rollover (preparation : Preparation) (page : UInt64) (bump : UInt8)
structure TransferPlan where
  instruction : Instruction
  source : Key
  mint : Key
  vault : Key
  authority : Key
  amount : UInt64
  sourceBefore : UInt64
  sourceAfter : UInt64
  vaultBefore : UInt64
  vaultAfter : UInt64
  decimals : UInt8
def invalidInstruction : ProgramError := 3 * 2^32
def notEnoughKeys : ProgramError := 11 * 2^32
def borrowFailed : ProgramError := 12 * 2^32
def historyMismatch : ProgramError := 0x41532003
def treeFull : ProgramError := 0x41532004
def nonCanonicalLeaf : ProgramError := 0x41532007
end PCA
