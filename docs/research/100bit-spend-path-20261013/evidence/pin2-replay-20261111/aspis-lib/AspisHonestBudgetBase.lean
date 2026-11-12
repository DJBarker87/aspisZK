import BinHonestStartFrames

set_option autoImplicit false
noncomputable section
namespace AspisHonestBudgetBase
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisR1 AspisR1.BinHonestStartFrames
/-- `BinHonestQueryBudget.raw`, carrier-free copy: the byte view of a recorded trace. -/
abbrev raw (tr : List (Addr L × State)) : List (Bytes × State) :=
  tr.map (fun q => (q.1.toBytes, q.2))
end AspisHonestBudgetBase
