import Port12COUNT_Installed
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port12COUNT_FirstReads
open Aeneas Aeneas.Std Result VTop_Stages
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw

/-- Total ordered call-log length is a sufficient metric for first reads.
Repeated addresses were counted in the source proofs and need not be fresh. -/
theorem checkpointChain (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State) (proof pub : Slice U8)
    (p0 : verifier.Prepared) (written : verifier.Accumulator) (folded0 folded1 : Array U8 32#usize) :
    firstReads emptyTable
      (eval H (Port12COUNT_Installed.checkpointChain reserved unwrap D hash proof pub p0 written folded0 folded1)).1≤1046 :=
  (VerifierCallBudget.firstReads_le_length emptyTable _).trans
    (Port12COUNT_Installed.checkpointChain_count reserved unwrap D hash H proof pub p0 written folded0 folded1)

/-- The ordered concatenation of the four ACTUAL installed call observations,
with every repeated source query, has first-read cost at most1046. Other
source calls interleaved by the complete driver remain external obligations. -/
theorem owned_calls (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : VTop_OracleCode.Implementation) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State) (proof pub ck : Slice U8)
    (p0 p1 : verifier.Prepared) (written : verifier.Accumulator)
    (folded0 folded1 : Array U8 32#usize) :
    let impl : VTop_OracleCode.Implementation := Port9OR_Installed.implementation ops reserved unwrap rest
    firstReads emptyTable
      ((eval H (impl (.op5 D proof p0 folded0 0#usize hash))).1 ++
       (eval H (impl (.op8 D p0 written proof pub hash))).1 ++
       (eval H (impl (.op18 D ck proof pub .S2 hash))).1 ++
       (eval H (impl (.op5 D proof p1 folded1 1#usize hash))).1)≤1046 := by
  have sufficient := VerifierCallBudget.firstReads_le_length emptyTable
      ((eval H (Port9OR_Installed.batch D hash proof p0 folded0 0#usize)).1 ++
       (eval H (Port9OR_Bodies.writer D p0 written proof pub hash)).1 ++
       (eval H (Port9OR_Bodies.reader reserved unwrap D ck proof pub .S2 hash)).1 ++
       (eval H (Port9OR_Installed.batch D hash proof p1 folded1 1#usize)).1)
  rw [List.length_append,List.length_append,List.length_append] at sufficient
  exact sufficient.trans (Port12COUNT_Installed.owned_calls ops reserved unwrap rest D hash H proof pub ck p0 p1 written folded0 folded1)

#print axioms checkpointChain
#print axioms owned_calls
end AspisR1.Port12COUNT_FirstReads
end
