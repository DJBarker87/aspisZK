import F3J_QueryPairs
import F3J_QueryRow
import F3J_LengthFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_QueryJoin
open Aeneas Aeneas.Std Result FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
open AspisR1PublicPreparation SourceDigestAddresses

/-- Exact ordered query-row log from successful source digest calls. The
unrolled source query body still has to supply `pairs`; no decoder equality
or whole-verifier acceptance is assumed or concluded here. -/
theorem ordered {Hash : Type} (D : aspis_core.Digest32 Hash) (hash : Hash)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (before absorbed : F3J_QueryPairs.RawState) (payload : Slice U8)
    (absorb : D.digest hash (CallerStep.openingAbsorbParts before 191#u8
      (UScalar.cast .U32 (Slice.len payload)) payload)=ok absorbed)
    (calls : List F3J_QueryPairs.Call) (pairs : F3J_QueryPairs.Pairs D hash 8 absorbed calls)
    (fits : payload.val.length<4294967296)
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) (b : LiteralTranscript.BytesMessage)
    (erased : LiteralTranscript.erase m=.payload b)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before)
    (framing : b.val=OraclePortCompactDraft.framed (MultiproofConeCanonical.bytesOf payload.val)) :
    (eval H (LiteralByteSampler.samp 31 P m).toProgram).1=
      (flatten (CallerStep.openingAbsorbParts before 191#u8
        (UScalar.cast .U32 (Slice.len payload)) payload),decodeState absorbed)::
      F3J_QueryPairs.observed calls := by
  let p := SelectedTranscriptParams.params
  have address : (UnifiedSampler.absorb p 31 (LiteralTranscript.erasePrefix P) b).toBytes=
      flatten (CallerStep.openingAbsorbParts before 191#u8
        (UScalar.cast .U32 (Slice.len payload)) payload) := by
    unfold UnifiedSampler.absorb
    rw [state,absorbA,Addr.toBytes_ofBytes,F3J_OpeningFrame.absorb]
    change AspisV8R19.DuplexFrames.absorb (bytes (decodeState before)) (decodeByte (191#u8)) b.val=_
    rw [framing,F3J_LengthFrame.framed payload fits]
    rfl
  have ha := backend _ ⟨hash,_,absorbed,rfl,absorb⟩
  change decodeState absorbed=H (flatten _) at ha
  rw [F3J_QueryRow.log H P m b erased]
  simp only [List.map_cons]
  rw [address,← ha,← F3J_QueryPairs.ordered D hash H backend pairs]

#print axioms ordered
end AspisR1.F3J_QueryJoin
end
