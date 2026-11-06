import NLP_RootCodec
import NLP_InputDomain
import NLP_ResumeRoots
set_option autoImplicit false
noncomputable section
namespace NLP_C04Roots
open Aeneas Aeneas.Std Result VTop_Stages AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
/-- Complete root bindings from SAME current byte projections. No callee
success or endpoint is an external premise of this algebraic lemma. -/
theorem bindings (ck proof : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize)
 (root0Input : NLP_InputDomain.Root0 ck proof)
 (root0Read : (Port3_BatchStage.root0 p).val=(ck.val.drop 112).take 32)
 (foldedRead : folded.val=(proof.val.drop 7751).take 32) :
 ∀ k : Fin 3,Port3_NativeBatchCalls.rootAt (NLL_BatchSource.roots p folded) k=
  encodeState (OraclePortBatchDraft.committedRoot
   (NLP_RootCodec.parsed proof (Port3_BatchStage.root1 p)) k.val) := by
 intro k
 have h0 : Port3_BatchStage.root0 p=encodeState
  ((SemanticRecordCodec.decodeState (OraclePortCompactDraft.slice
   (MultiproofConeCanonical.bytesOf proof.val) 16 32)).getD (fun _=>0)) :=
  Subtype.ext (root0Read.trans root0Input)
 have h2 : encodeState (OraclePortBatchDraft.committedRoot
  (NLP_RootCodec.parsed proof (Port3_BatchStage.root1 p)) 2)=folded := by
  change encodeState ((SemanticRecordCodec.decodeState
   (OraclePortCompactDraft.slice (MultiproofConeCanonical.bytesOf proof.val) 7751 32)).getD (fun _=>0))=folded
  have same : OraclePortCompactDraft.slice (MultiproofConeCanonical.bytesOf proof.val) 7751 32=
   MultiproofConeCanonical.bytesOf folded.val := by
   rw [foldedRead]
   simp only [OraclePortCompactDraft.slice,MultiproofConeCanonical.bytesOf,List.map_drop,List.map_take]
  rw [same]
  exact NLP_RootCodec.decode_array folded
 fin_cases k
 · change Port3_BatchStage.root0 p=encodeState (OraclePortBatchDraft.committedRoot _ 0)
   rw [NLP_RootDomain.kind0_fixed proof _ (NLP_RootCodec.wire _ _)]
   exact h0
 · change Port3_BatchStage.root1 p=encodeState (OraclePortBatchDraft.committedRoot _ 1)
   exact (NLP_RootCodec.kind1 _ _).symm
 · change folded=encodeState (OraclePortBatchDraft.committedRoot _ 2)
   exact h2.symm
set_option pp.proofs false
#print bindings
#print axioms bindings
end NLP_C04Roots
