import NLN_TX2_053
import MultiproofConePhysicalTransport
set_option autoImplicit false
noncomputable section
namespace NLP_RootDomain
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
/-- The first NLN root binding is fixed by the proof wire, independently of
which semantic-list witness is chosen. -/
theorem kind0_fixed (proof : Slice U8) (parsed : OraclePortCompactDraft.Parsed)
 (wire : parsed.wire=MultiproofConeCanonical.bytesOf proof.val) :
 OraclePortBatchDraft.committedRoot parsed 0=
 (SemanticRecordCodec.decodeState (OraclePortCompactDraft.slice
  (MultiproofConeCanonical.bytesOf proof.val) 16 32)).getD (fun _=>0) := by
 simp only [OraclePortBatchDraft.committedRoot,ite_true,OraclePortCompactDraft.root0,wire]
/-- Necessary own-argument clause at C04; selecting Parsed.semantic cannot
repair a mismatch between the resumed checkpoint root and the proof root. -/
theorem necessary (proof : Slice U8) (parsed : OraclePortCompactDraft.Parsed)
 (wire : parsed.wire=MultiproofConeCanonical.bytesOf proof.val)
 (p : verifier.Prepared) (folded : Array U8 32#usize)
 (roots : ∀ k : Fin 3,Port3_NativeBatchCalls.rootAt (NLL_BatchSource.roots p folded) k=
  encodeState (OraclePortBatchDraft.committedRoot parsed k.val)) :
 Port3_BatchStage.root0 p=encodeState
  ((SemanticRecordCodec.decodeState (OraclePortCompactDraft.slice
   (MultiproofConeCanonical.bytesOf proof.val) 16 32)).getD (fun _=>0)) := by
 have h:=roots ⟨0,by decide⟩
 change Port3_BatchStage.root0 p=encodeState (OraclePortBatchDraft.committedRoot parsed 0) at h
 rw [kind0_fixed proof parsed wire] at h
 exact h
/-- Explicit obstruction on arbitrary input carriers, not a claim that this
condition is reached by the deployed authenticated caller. -/
theorem mismatch (proof : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize)
 (different : Port3_BatchStage.root0 p≠encodeState
  ((SemanticRecordCodec.decodeState (OraclePortCompactDraft.slice
   (MultiproofConeCanonical.bytesOf proof.val) 16 32)).getD (fun _=>0))) :
 ¬∃ parsed : OraclePortCompactDraft.Parsed,
  parsed.wire=MultiproofConeCanonical.bytesOf proof.val ∧
  ∀ k : Fin 3,Port3_NativeBatchCalls.rootAt (NLL_BatchSource.roots p folded) k=
   encodeState (OraclePortBatchDraft.committedRoot parsed k.val) := by
 rintro ⟨parsed,wire,roots⟩
 exact different (necessary proof parsed wire p folded roots)
#print kind0_fixed
#print necessary
#print mismatch
#print axioms kind0_fixed
#print axioms necessary
#print axioms mismatch
end NLP_RootDomain
