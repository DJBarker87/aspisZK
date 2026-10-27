import F3L_AlignedPrefix
import F3L_SamplerMessages
import F3L_SamplerStatement
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_SamplerAligned
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open OraclePortCompactDraft
attribute [local irreducible] F3J_InputRows.proof F3J_SamplerRun.program

theorem aligned (H : Bytes → State) (p : Parsed) (root : State)
    (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (pub : LiteralTranscript.Public) (tag : pub.tag=p.wire[8]?.getD 0)
    (parsedPublic : ∃ decoded,SemanticPublicWire.parsePublic pub.pubBytes=some decoded)
    (rootBytes : bytes root=root0 p) :
    Aligned p (LiteralTranscript.erasePrefix (eval H
      (F3J_SamplerRun.program (F3J_InputRows.proof p root w bound) 0 33 (FS.emptyPrefix pub))).2) := by
  let pf := F3J_InputRows.proof p root w bound
  let Q := (eval H (F3J_SamplerRun.program pf 0 33 (FS.emptyPrefix pub))).2
  have statement : Q.statement=pub := F3L_SamplerStatement.statement H pf 0 33 (FS.emptyPrefix pub)
  exact F3L_AlignedPrefix.aligned p root w bound Q
    (statement ▸ tag) (statement ▸ parsedPublic)
    (F3J_SamplerRun.length H pf 0 33 (FS.emptyPrefix pub)) rootBytes
    (fun row h=>F3L_SamplerMessages.entry H pf pub 33 row h)

#print axioms aligned
end AspisR1.F3L_SamplerAligned
end
