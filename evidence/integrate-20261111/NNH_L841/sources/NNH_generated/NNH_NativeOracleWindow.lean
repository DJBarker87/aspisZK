import NNH_NativeOracleReply
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_NativeOracleWindow
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NNH_NativeOracleSlots
variable (H : Bytes → State) (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
 (clock : Except RSL.ProgramError UInt64) (r : NP6_StdModel.Reservation)

theorem merkle {X : Type} (d : VTop_Stages.aspis_core.digest.Digest32 X) (hash : X)
 (proof : Slice U8) (len : proof.val.length = 57607)
 (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire = MultiproofConeCanonical.bytesOf proof.val)
 (p : VTop_Stages.verifier.Prepared) (folded : Array U8 32#usize)
 (reply : NJU_CommonObserved.R Unit)
 (input : NLT_NativeWindows.Input (.merkle proof p folded reply))
 (canonical : ∀ j, j < 22 → p.queries.val[j]!.val < 262144)
 (inside : NLL.History) (out : NLL.Reply)
 (native : NLL_BatchSource.Invocation (part H pda clock r) proof p folded 1#usize inside out) :
 NLT_NativeWindows.window (part H pda clock r) d hash (.merkle proof p folded reply) input =
 NLT_NativeWindows.window H d hash (.merkle proof p folded reply) input := by
 simp only [NLT_NativeWindows.window]
 rw [NNH_NativeOracleReply.action H pda clock r d hash proof len parsed wire p folded canonical inside out native]

/-- Transport the detailed window once the SAME returning C04 occurrence's
original domain has been derived. This is a local slot lemma, not the final
064/host producer; aborting windows and caller-domain derivation remain open. -/
def detail {X : Type} (d : VTop_Stages.aspis_core.digest.Digest32 X) (hash : X)
 (proof : Slice U8) (len : proof.val.length = 57607)
 (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire = MultiproofConeCanonical.bytesOf proof.val)
 (p : VTop_Stages.verifier.Prepared) (folded : Array U8 32#usize)
 (reply : NJU_CommonObserved.R Unit)
 (input : NLT_NativeWindows.Input (.merkle proof p folded reply))
 (canonical : ∀ j, j < 22 → p.queries.val[j]!.val < 262144)
 (inside : NLL.History) (out : NLL.Reply)
 (native : NLL_BatchSource.Invocation (part H pda clock r) proof p folded 1#usize inside out)
 (source : NLT_Subcuts.Detail (part H pda clock r)
  (NLT_NativeWindows.window (part H pda clock r) d hash (.merkle proof p folded reply) input)) :
 NLT_Subcuts.Detail H (NLT_NativeWindows.window H d hash (.merkle proof p folded reply) input) := by
 have next := NNH_NativeOracleDetail.transport H pda clock r source
 rw [merkle H pda clock r d hash proof len parsed wire p folded reply input canonical inside out native] at next
 exact next
#print axioms merkle
#print axioms detail
end AspisR1.NNH_NativeOracleWindow
end
