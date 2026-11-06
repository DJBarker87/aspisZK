set_option autoImplicit false
namespace PCA
inductive DepositError where
  | WrongLength
  | WrongMagic
  | WrongVersion
  | NonZeroReserved
  | InvalidAmount
  | InvalidPayloadLength
  | NonCanonicalDigest
  deriving DecidableEq
inductive TreeError where
  | TreeFull
  | InsufficientCapacity
  | IndexOutOfRange
  | RootMismatch
  | NonCanonicalFrontier
  | WrongLength
  | WrongMagic
  | WrongVersion
  | WrongDepth
  | WrongTreeHash
  | WrongDigestEncoding
  | NonCanonicalDigest
  | NonZeroReserved
  deriving DecidableEq
inductive ForestError where
  | WrongLength
  | WrongMagic
  | WrongVersion
  | WrongLaneCount
  | WrongDigestEncoding
  | WrongDepth
  | WrongFormatBinding
  | NonZeroReserved
  | ZeroRequiredBinding
  | InvalidBoolean
  | InvalidMasterState
  | InvalidLane
  | LaneMasterMismatch
  | LaneOrderMismatch
  | LaneSequenceDecreased
  | DuplicateCheckpoint
  | CheckpointSequenceOverflow
  | NonCanonicalDigest
  | Identity
  | Policy
  | Tree (error : TreeError)
  deriving DecidableEq
inductive LeafError where
  | NonCanonicalCommitment
  | NonCanonicalOccupancy
  | NonCanonicalInverse
  | OccupancyNotBoolean
  | SentinelInverseMismatch
  | EmptyInverseNonZero
  | EmptyCommitmentNonZero
  | OccupiedSentinelZero
  | SelectedSlotEmpty
  deriving DecidableEq
inductive Failure where
  | program (code : UInt64)
  | deposit (error : DepositError)
  | forest (error : ForestError)
  | leaf (error : LeafError)
  deriving DecidableEq
instance : Coe UInt64 Failure := ⟨Failure.program⟩
end PCA
