import RPz7_F3K_RhoJoin
import RPz7_F3K_SamplerOne
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_RhoOne
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw

theorem rho {Hash : Type} (D : aspis_core.Digest32 Hash) (B : PreparedModel.Boundaries)
    (before after : transcript.Transcript Hash) (payload : Slice U8)
    (value : aspis_core.field.QM31)
    (success : PreparedModel.scalar_k B D before 32#u8 payload=ok (value,after))
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (p : Parsed) (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (frame : rowBytes p 32=framed (MultiproofConeCanonical.bytesOf payload.val))
    (fits : payload.val.length<4294967296) (P : LiteralTranscript.Prefix)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before.state) :
    let pf := F3J_InputRows.proof p root w bound
    (eval H (F3J_SamplerRun.program pf 32 1 P)).1=
      observe (run (PreparedScalarEffects.scalar_k effects B D before 32#u8 payload)).1 ∧
    UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program pf 32 1 P)).2)=decodeState after.state := by
  let pf := F3J_InputRows.proof p root w bound
  have joined := F3K_RhoJoin.rho D B before after payload value success H backend
    p root w bound frame fits P state
  have one := F3K_SamplerOne.one H pf 32 P
  constructor
  · exact (congrArg Prod.fst one).trans joined.1
  · rw [one]
    change UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix (F3K_SamplerOne.next H pf 32 P))=_
    rw [F3K_SamplerOne.state]
    exact joined.2

#print axioms rho
end AspisR1.F3K_RhoOne
end
