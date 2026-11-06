import NLL_Tx2AtActual
import NLN_TX2_053
set_option autoImplicit false
noncomputable section
namespace NLP_C04Query
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
/-- All scalar/extent clauses at C04 are derived from THAT source occurrence.
The wire and root provenance remain separate obligations, not hidden here. -/
theorem domain (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (len : proof.val.length=57607)
 (enteredProof : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize) (reply : R Unit)
 (entered : Event.merkle enteredProof p folded reply∈(run wr rr merkle finish d pub proof ck hash none).events) :
 enteredProof=proof ∧ enteredProof.val.length=57607 ∧
 ∀ j,j<22 → p.queries.val[j]!.val<262144 := by
 obtain ⟨same,a,resumed,canonical⟩:=NLL_Tx2AtActual.source wr rr merkle finish d pub proof ck hash enteredProof p folded reply entered
 exact ⟨same,by rw [same]; exact len,canonical⟩
/-- Auxiliary installation only: wire/root bindings are still visibly open.
The complete NLN packet, including returning/aborting histories, is preserved. -/
theorem packet (H : Bytes → State)
 (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (len : proof.val.length=57607)
 (enteredProof : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize) (reply : R Unit)
 (entered : Event.merkle enteredProof p folded reply∈(run wr rr merkle finish d pub proof ck hash none).events)
 (parsed : OraclePortCompactDraft.Parsed)
 (wire : parsed.wire=MultiproofConeCanonical.bytesOf proof.val)
 (roots : ∀ k : Fin 3, Port3_NativeBatchCalls.rootAt (NLL_BatchSource.roots p folded) k=
  encodeState (OraclePortBatchDraft.committedRoot parsed k.val)) :
 NLN.BatchPacket H enteredProof parsed p folded 1#usize := by
 obtain ⟨same,extent,canonical⟩:=domain wr rr merkle finish d pub proof ck hash len enteredProof p folded reply entered
 apply NLN_TX2_053.root H enteredProof extent parsed
 · rw [same]; exact wire
 · exact canonical
 · exact roots
#print domain
#print packet
#print axioms domain
#print axioms packet
end NLP_C04Query
