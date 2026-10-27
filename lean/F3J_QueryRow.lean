import F3J_QueryLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_QueryRow
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem log (H : Bytes → State) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) (b : LiteralTranscript.BytesMessage)
    (erased : LiteralTranscript.erase m=.payload b) :
    (eval H (LiteralByteSampler.samp 31 P m).toProgram).1=
      let p := SelectedTranscriptParams.params
      let a := UnifiedSampler.absorb p 31 (LiteralTranscript.erasePrefix P) b
      ((a,H a.toBytes)::F3J_QueryLog.issued p (fun a => H a.toBytes) 8 (H a.toBytes)).map
        (fun entry => (entry.1.toBytes,entry.2)) := by
  rw [LiteralByteSampler.eval_eq]
  change (mapView Addr.toBytes (eval (fun a => H a.toBytes)
    (UnifiedSampler.samp SelectedTranscriptParams.params _ 31
      (LiteralTranscript.erasePrefix P) (LiteralTranscript.erase m)).toProgram)).1=_
  rw [erased,UnifiedSampler.row_query]
  simp only [mapView]
  rw [F3J_QueryLog.sampler]

theorem length (H : Bytes → State) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) (b : LiteralTranscript.BytesMessage)
    (erased : LiteralTranscript.erase m=.payload b) :
    (eval H (LiteralByteSampler.samp 31 P m).toProgram).1.length=17 := by
  rw [log H P m b erased]
  simp only [List.length_map,List.length_cons,F3J_QueryLog.length]

#print axioms log
#print axioms length
end AspisR1.F3J_QueryRow
end
