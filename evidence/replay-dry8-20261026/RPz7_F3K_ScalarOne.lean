import RPz7_F3K_ScalarJoin
import RPz7_F3K_SamplerOne
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_ScalarOne
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw

theorem scalar {Hash : Type} (D : aspis_core.Digest32 Hash) (B : PreparedModel.Boundaries)
    (before after : transcript.Transcript Hash) (row : U8) (payload : Slice U8)
    (value : aspis_core.field.WideExact) (nonzero : Bool)
    (success : PreparedModel.scalar B D before row payload nonzero=ok (value,after))
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (p : Parsed) (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (schedule : row.val=27 ∨ row.val=28 ∨ row.val=29 ∨ row.val=30)
    (frame : rowBytes p row.val=framed (MultiproofConeCanonical.bytesOf payload.val))
    (fits : payload.val.length<4294967296) (P : LiteralTranscript.Prefix)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before.state) :
    let pf := F3J_InputRows.proof p root w bound
    (eval H (F3J_SamplerRun.program pf row.val 1 P)).1=
      observe (run (PreparedScalarEffects.scalar effects B D before row payload nonzero)).1 ∧
    UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program pf row.val 1 P)).2)=decodeState after.state := by
  let pf := F3J_InputRows.proof p root w bound
  have joined := F3K_ScalarJoin.scalar D B before after row payload value nonzero success H backend
    p root w bound schedule frame fits P state
  have one := F3K_SamplerOne.one H pf row.val P
  constructor
  · exact (congrArg Prod.fst one).trans joined.1
  · rw [one]
    change UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix (F3K_SamplerOne.next H pf row.val P))=_
    rw [F3K_SamplerOne.state]
    exact joined.2

#print axioms scalar
end AspisR1.F3K_ScalarOne
end
