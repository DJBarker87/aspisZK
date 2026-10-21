import OraclePortCheckpointResumeC5
import OraclePortCheckpointPreparedC5

/-! Explicit three-read writer and three-read resumer. No oracle-dependent
checkpoint is supplied as a supposedly fixed input to the experiment. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortCheckpointOracleC5
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OraclePortCheckpointStateC3.advance OraclePortCheckpointStateC3.write
  QueryAccumulator.run QueryAccumulator.run22

def writer (stored pub : Bytes) (p : Prepared) (a : QueryAccumulator.State K E) :
    Program Bytes State Carrier :=
  .ask stored fun hp => .ask pub fun hu =>
    let b := body p a hp hu
    .ask (OraclePortPhysicalFrameDraft.domain ++ b) fun hc => .done ⟨stored,b ++ bytes hc⟩

theorem writer_value (H : Bytes → State) (stored pub : Bytes) (p : Prepared)
    (a : QueryAccumulator.State K E) :
    (eval H (writer stored pub p a)).2 = ⟨stored,encode H stored pub p a⟩ := rfl

theorem writer_reads (H : Bytes → State) (stored pub : Bytes) (p : Prepared)
    (a : QueryAccumulator.State K E) : (eval H (writer stored pub p a)).1.length = 3 := rfl

/-- All prepared fields are decoded from the actual saved bytes. The full
proof slice is retained for the separate source-data reconstruction. -/
def finishResume (d : MatchingSupport.Data E) (saved : Carrier) : Option (QueryAccumulator.State K E) := do
  let p ← OraclePortCheckpointPreparedC5.decode saved.checkpoint
  let a ← decodeAccumulator saved.checkpoint
  pure (OraclePortCheckpointStateC3.advance (model d p.rho p.queries) 12 a)

def resumer (pub : Bytes) (d : MatchingSupport.Data E) (saved : Carrier) :
    Program Bytes State (Option (QueryAccumulator.State K E)) :=
  .ask saved.stored fun hp => .ask pub fun hu =>
    .ask (OraclePortPhysicalFrameDraft.domain ++ saved.checkpoint.take 1736) fun hc =>
      .done (if saved.checkpoint.length = 1768 ∧
        slice saved.checkpoint 16 32 = bytes hp ∧ slice saved.checkpoint 48 32 = bytes hu ∧
        saved.checkpoint.drop 1736 = bytes hc then finishResume d saved else none)

theorem resumer_reads (H : Bytes → State) (pub : Bytes) (d : MatchingSupport.Data E)
    (saved : Carrier) : (eval H (resumer pub d saved)).1.length = 3 := rfl

theorem resumer_on_binding (H : Bytes → State) (pub : Bytes)
    (d : MatchingSupport.Data E) (saved : Carrier) (binding : HashBinding H pub saved) :
    (eval H (resumer pub d saved)).2 = finishResume d saved := by
  simp only [resumer,eval]
  exact if_pos binding

theorem resumer_value (H : Bytes → State) (stored pub : Bytes) (c : Context)
    (d : MatchingSupport.Data E) (rho : K) (q : Fin 22 → Fin 262144) :
    (eval H (resumer pub d (save H stored pub c d rho q))).2 =
      some (QueryAccumulator.run22 LiteralOpeningView.eK rho
        (QueryResidualBridge.values d q) (QueryResidualBridge.basis q)) := by
  have binding := save_hash_binding H stored pub c d rho q
  rw [resumer_on_binding H pub d _ binding]
  unfold finishResume
  have decodedP := OraclePortCheckpointPreparedC5.decode_encode H stored pub
    (prepared c d rho q) (OraclePortCheckpointStateC3.write (model d rho q)).accumulator
  have decodedA := decode_written H stored pub (prepared c d rho q)
    (OraclePortCheckpointStateC3.write (model d rho q)).accumulator
    (OraclePortCheckpointStateC3.saved_next _)
  change (do
    let p ← OraclePortCheckpointPreparedC5.decode (encode H stored pub _ _)
    let a ← decodeAccumulator (encode H stored pub _ _)
    pure (OraclePortCheckpointStateC3.advance (model d p.rho p.queries) 12 a)) = _
  rw [decodedP,decodedA]
  simp only [Option.bind_eq_bind,Option.bind_some]
  have result := physical_resume H stored pub c d rho q
  rw [resume,if_pos binding] at result
  change (decodeAccumulator (encode H stored pub _ _)).map _ = _ at result
  rw [decodedA,Option.map_some] at result
  exact result

/-- Six checkpoint hashes, including both full-proof reads, remain visible
in the program trace. This does not install a completed verifier decision. -/
def writeResume (stored pub : Bytes) (c : Context) (d : MatchingSupport.Data E)
    (rho : K) (q : Fin 22 → Fin 262144) : Program Bytes State (Option (QueryAccumulator.State K E)) :=
  bind (writer stored pub (prepared c d rho q)
    (OraclePortCheckpointStateC3.write (model d rho q)).accumulator) (resumer pub d)

theorem writeResume_value (H : Bytes → State) (stored pub : Bytes) (c : Context)
    (d : MatchingSupport.Data E) (rho : K) (q : Fin 22 → Fin 262144) :
    (eval H (writeResume stored pub c d rho q)).2 =
      some (QueryAccumulator.run22 LiteralOpeningView.eK rho
        (QueryResidualBridge.values d q) (QueryResidualBridge.basis q)) := by
  simp only [writeResume,eval_bind,writer_value]
  exact resumer_value H stored pub c d rho q

theorem writeResume_reads (H : Bytes → State) (stored pub : Bytes) (c : Context)
    (d : MatchingSupport.Data E) (rho : K) (q : Fin 22 → Fin 262144) :
    (eval H (writeResume stored pub c d rho q)).1.length = 6 := by
  simp only [writeResume,eval_bind,List.length_append,writer_reads,resumer_reads]

#print axioms writer_value
#print axioms writer_reads
#print axioms resumer_reads
#print axioms resumer_on_binding
#print axioms resumer_value
#print axioms writeResume_value
#print axioms writeResume_reads
end AspisR1.OraclePortCheckpointOracleC5
end
