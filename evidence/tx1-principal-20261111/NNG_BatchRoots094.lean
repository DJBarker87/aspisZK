import LIBC_BatchMerkle
import MultiproofConePhysicalTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_BatchRoots094
open Aeneas Aeneas.Std Result AspisR1Stage2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
abbrev Digest := Array U8 32#usize
/-- The wire is the original proof. The existential semantic row supplies the
actual second stored root; LIBC_BatchWire proves that the source history uses
only this wire and the supplied roots, independently of that row witness. -/
def parsed (proof : Slice U8) (root1 : Digest) : OraclePortCompactDraft.Parsed :=
 ⟨MultiproofConeCanonical.bytesOf proof.val,[[],[],[0,0,0,0,0]++bytes (decodeState root1)]⟩

theorem root_payload (proof : Slice U8) (root : Digest) (offset : Nat)
 (same : root.val=(proof.val.drop offset).take 32) :
 OraclePortCompactDraft.slice (MultiproofConeCanonical.bytesOf proof.val) offset 32=bytes (decodeState root) := by
 rw [MultiproofConePhysicalTransport.digest_bytes,same]
 simp only [OraclePortCompactDraft.slice,MultiproofConeCanonical.bytesOf,List.map_drop,List.map_take]
#print axioms root_payload

theorem values (proof : Slice U8) (root0 root1 folded : Digest)
 (first : root0.val=(proof.val.drop 16).take 32)
 (third : folded.val=(proof.val.drop 7751).take 32) :
 ∀ k : Fin 3,Port3_NativeBatchCalls.rootAt (Array.make 3#usize [root0,root1,folded]) k=
 encodeState (OraclePortBatchDraft.committedRoot (parsed proof root1) k.val) := by
 intro k
 fin_cases k
 · change root0=encodeState ((SemanticRecordCodec.decodeState
    (OraclePortCompactDraft.slice (MultiproofConeCanonical.bytesOf proof.val) 16 32)).getD (fun _=>0))
   rw [root_payload proof root0 16 first,SemanticRecordCodec.decodeState_bytes]
   exact (array_roundtrip root0).symm
 · change root1=encodeState ((SemanticRecordCodec.decodeState (bytes (decodeState root1))).getD (fun _=>0))
   rw [SemanticRecordCodec.decodeState_bytes]
   exact (array_roundtrip root1).symm
 · change folded=encodeState ((SemanticRecordCodec.decodeState
    (OraclePortCompactDraft.slice (MultiproofConeCanonical.bytesOf proof.val) 7751 32)).getD (fun _=>0))
   rw [root_payload proof folded 7751 third,SemanticRecordCodec.decodeState_bytes]
   exact (array_roundtrip folded).symm
#print axioms values

theorem source_roots (p : AspisR1Stage2.verifier.Prepared) (root0 root1 folded : Digest)
 (same : p.roots=Array.make 2#usize [root0,root1]) :
 NLL_BatchSource.roots p folded=Array.make 3#usize [root0,root1,folded] := by
 have first : Port3_BatchStage.root0 p=root0 :=
  congrArg (fun r : Array Digest 2#usize=>r.val[0]'(by rw [r.property];decide)) same
 have second : Port3_BatchStage.root1 p=root1 :=
  congrArg (fun r : Array Digest 2#usize=>r.val[1]'(by rw [r.property];decide)) same
 apply Subtype.ext
 change [Port3_BatchStage.root0 p,Port3_BatchStage.root1 p,folded]=[root0,root1,folded]
 rw [first,second]
#print axioms source_roots
end AspisR1.NNG_BatchRoots094
