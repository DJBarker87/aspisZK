import F3K_QueryChain
import F3J_PhysicalQuery
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_QueryLog
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw

theorem ordered {Hash : Type} (B : QueriesModel.Boundaries) (D : aspis_core.Digest32 Hash)
    (before after : transcript.Transcript Hash) (payload : Slice U8) (q : Array U32 22#usize)
    (success : QueriesModel.queries B D before 31#u8 payload=ok (.Ok q,after))
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (fits : payload.val.length<4294967296)
    (p : OraclePortCompactDraft.Parsed) (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(OraclePortCompactDraft.rowBytes p row).length≤SelectedTranscriptParams.D)
    (frame : OraclePortCompactDraft.rowBytes p 31=OraclePortCompactDraft.framed (MultiproofConeCanonical.bytesOf payload.val))
    (P : LiteralTranscript.Prefix)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before.state) :
    ∃ absorbed calls,
      transcript.Transcript.absorb D before 31#u8 payload=ok absorbed ∧
      F3J_QueryPairs.Pairs D absorbed.hash 8 absorbed.state calls ∧
      (eval H (LiteralByteSampler.samp 31 P (F3J_InputRows.proof p root w bound 31)).toProgram).1=
        (flatten (CallerStep.openingAbsorbParts before.state 191#u8
          (UScalar.cast .U32 (Slice.len payload)) payload),decodeState absorbed.state)::
        F3J_QueryPairs.observed calls := by
  obtain ⟨absorbed,calls,ha,hpairs⟩ := F3K_QueryChain.chain B D before after 31#u8 payload q success
  exact ⟨absorbed,calls,ha,hpairs,F3J_PhysicalQuery.ordered D before absorbed payload ha H backend
    calls hpairs fits p root w bound frame P state⟩

#print axioms ordered
end AspisR1.F3K_QueryLog
end
