import NNH_NativeOracleDetail
import NLL_BatchReturning
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_NativeOracleReply
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NNH_NativeOracleSlots
variable (H : Bytes → State) (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
 (clock : Except RSL.ProgramError UInt64) (r : NP6_StdModel.Reservation)
/-- Pointwise C04 Result transport on the CLOSED child's original domain.
The outer064 consumer must derive the domain at this SAME entered occurrence;
none of these clauses is an allowed new final-headline hypothesis. -/
theorem action {X : Type} (d : VTop_Stages.aspis_core.digest.Digest32 X) (hash : X)
 (proof : Slice U8) (len : proof.val.length = 57607)
 (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire = MultiproofConeCanonical.bytesOf proof.val)
 (p : VTop_Stages.verifier.Prepared) (folded : Array U8 32#usize)
 (canonical : ∀ j, j < 22 → p.queries.val[j]!.val < 262144)
 (inside : NLL.History) (out : NLL.Reply)
 (native : NLL_BatchSource.Invocation (part H pda clock r) proof
  p folded 1#usize inside out) :
 NLP_NativeMerkle.action (part H pda clock r) d proof p folded 1#usize hash =
 NLP_NativeMerkle.action H d proof p folded 1#usize hash := by
 have old := NLL_BatchReturning.source (part H pda clock r) proof len parsed wire
  p folded 1#usize (by scalar_tac) canonical inside out native
 have changed := NNH_NativeOracleBatch.returning H pda clock r proof
  p folded 1#usize inside out native
 have next := NLL_BatchReturning.source H proof len parsed wire
  p folded 1#usize (by scalar_tac) canonical inside out changed
 unfold NLP_NativeMerkle.action
 rw [old.1,next.1]
#print axioms action
end AspisR1.NNH_NativeOracleReply
end
