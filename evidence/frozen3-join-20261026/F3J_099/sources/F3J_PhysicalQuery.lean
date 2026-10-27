import F3J_QueryAbsorber
import F3J_InputRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_PhysicalQuery
open Aeneas Aeneas.Std Result FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
open AspisR1PublicPreparation SourceDigestAddresses OraclePortCompactDraft

/-- Specializes the seventeen ordered query calls to the constructed physical
proof's row31. Extracting the full `pairs` chain from the installed query body,
and equating its selected decoder state, remain separate obligations. -/
theorem ordered {Hash : Type} (D : aspis_core.Digest32 Hash)
    (before absorbed : transcript.Transcript Hash) (payload : Slice U8)
    (success : transcript.Transcript.absorb D before 31#u8 payload=ok absorbed)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (calls : List F3J_QueryPairs.Call)
    (pairs : F3J_QueryPairs.Pairs D absorbed.hash 8 absorbed.state calls)
    (fits : payload.val.length<4294967296)
    (p : Parsed) (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (frame : rowBytes p 31=framed (MultiproofConeCanonical.bytesOf payload.val))
    (P : LiteralTranscript.Prefix)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before.state) :
    (eval H (LiteralByteSampler.samp 31 P (F3J_InputRows.proof p root w bound 31)).toProgram).1=
      (flatten (CallerStep.openingAbsorbParts before.state 191#u8
        (UScalar.cast .U32 (Slice.len payload)) payload),decodeState absorbed.state)::
      F3J_QueryPairs.observed calls := by
  exact F3J_QueryAbsorber.ordered D before absorbed payload success H backend calls pairs fits
    P (F3J_InputRows.proof p root w bound 31) ⟨rowBytes p 31,bound 31⟩
    (by rw [F3J_InputRows.erased,if_neg (by decide)]) state frame

#print axioms ordered
end AspisR1.F3J_PhysicalQuery
end
