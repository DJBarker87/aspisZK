import RPz7_F3J_QueryJoin
import RPz7_F3J_OpeningFacts
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_QueryAbsorber
open Aeneas Aeneas.Std Result FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
open AspisR1PublicPreparation SourceDigestAddresses

theorem ordered {Hash : Type} (D : aspis_core.Digest32 Hash)
    (before absorbed : transcript.Transcript Hash) (payload : Slice U8)
    (success : transcript.Transcript.absorb D before 31#u8 payload=ok absorbed)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (calls : List F3J_QueryPairs.Call)
    (pairs : F3J_QueryPairs.Pairs D absorbed.hash 8 absorbed.state calls)
    (fits : payload.val.length<4294967296)
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) (b : LiteralTranscript.BytesMessage)
    (erased : LiteralTranscript.erase m=.payload b)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before.state)
    (framing : b.val=OraclePortCompactDraft.framed (MultiproofConeCanonical.bytesOf payload.val)) :
    (eval H (LiteralByteSampler.samp 31 P m).toProgram).1=
      (flatten (CallerStep.openingAbsorbParts before.state 191#u8
        (UScalar.cast .U32 (Slice.len payload)) payload),decodeState absorbed.state)::
      F3J_QueryPairs.observed calls := by
  obtain ⟨tag,digestState,add,digest,carried⟩ := PAln_OpeningCalls.absorb_success D before absorbed 31#u8 payload success
  change ok (191#u8)=ok tag at add
  cases Result.ok.inj add
  have hs : absorbed.state=digestState := congrArg (fun t => t.state) carried
  have hh : absorbed.hash=before.hash := congrArg (fun t => t.hash) carried
  rw [hh] at pairs
  have digest' : D.digest before.hash (CallerStep.openingAbsorbParts before.state 191#u8
      (UScalar.cast .U32 (Slice.len payload)) payload)=ok absorbed.state := by
    rw [hs]
    exact digest
  exact F3J_QueryJoin.ordered D before.hash H backend before.state absorbed.state payload
    digest' calls pairs fits P m b erased state framing

#print axioms ordered
end AspisR1.F3J_QueryAbsorber
end
