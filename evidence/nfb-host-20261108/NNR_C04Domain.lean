import NNR_Oracle
import NNH_NativeOracleWindow
import NLP_C04Query
import NLT_NativeFacts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNR_C04Domain
open Aeneas Aeneas.Std Result VTop_Stages NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NLT_NativeInvocation
/-- The exact C04 arguments at a common-parent occurrence; Root0-free. -/
theorem at_record (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) (len : proof.val.length = 57607)
 (result : R Unit) (records : List (Occurrence H d hash))
 (native : Invocation H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) result records)
 (record : Occurrence H d hash) (member : record ∈ records)
 (pr : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize) (reply : R Unit)
 (merkle : actual record = Event.merkle pr p folded reply) :
 pr = proof ∧ pr.val.length = 57607 ∧ ∀ j, j < 22 → p.queries.val[j]!.val < 262144 := by
 have entered := NLT_NativeFacts.member H d pub proof ck hash len result records native record member
 rw [merkle] at entered
 exact NLP_C04Query.domain _ _ _ _ d pub proof ck hash len pr p folded reply entered
#print axioms at_record
end AspisR1.NNR_C04Domain
end
