import NNP_ResumeHeader
set_option autoImplicit false
noncomputable section
namespace NNP_PartitionObstruction
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- A legal total Env reply function that distinguishes physical partitions. -/
def sha (parts : List RSL.Bytes) : RSL.B32 :=
 if parts.length = 1 then RSL.zero32 else RSL.B32.ofFill 1

theorem partition_length (b : RSL.Bytes) : (LIBB_C04Partition.partition b).length = 3 := by
 unfold LIBB_C04Partition.partition
 split <;> rfl

/-- Even a total Env sha256 need not identify singleton and C04 replies.
This is a counterexample to a universal hash-agreement premise, not a claim
that a particular accepted native execution exists in this Env. -/
theorem distinct (base : RSL.Env) (message : Bytes) :
 LIBB_HashModel.H {base with sha256 := sha} message ≠
 LIBB_PartitionEnv.H {base with sha256 := sha} message := by
 intro h
 have single : LIBB_HashModel.H {base with sha256 := sha} message =
  LIBB_HashModel.state RSL.zero32 := by
  unfold LIBB_HashModel.H sha
  rfl
 have partitioned : LIBB_PartitionEnv.H {base with sha256 := sha} message =
  LIBB_HashModel.state (RSL.B32.ofFill 1) := by
  unfold LIBB_PartitionEnv.H sha
  rw [partition_length]
  rfl
 rw [single,partitioned] at h
 have key := congrArg (fun s => NNC_ResumeEvents.digest
  (AspisV8R19.SqueezeOracleBridge.encodeState s)) h
 rw [LIBB_HashModel.state_exact,LIBB_HashModel.state_exact] at key
 have first := congrArg (fun k : RSL.B32 => k.bytes.head?) key
 have impossible : (0 : UInt8) = 1 := by
  simpa only [RSL.zero32,RSL.B32.ofFill,List.head?_replicate,Option.some.injEq] using first
 exact (by decide : (0 : UInt8) ≠ 1) impossible

theorem agreement_not_universal (base : RSL.Env) (proof pub : Bytes) :
 ¬ NNP_ResumeHeader.HeaderAgreement {base with sha256 := sha} proof pub := by
 intro h
 exact distinct base proof h.1

#print axioms partition_length
#print axioms distinct
#print axioms agreement_not_universal
end NNP_PartitionObstruction
