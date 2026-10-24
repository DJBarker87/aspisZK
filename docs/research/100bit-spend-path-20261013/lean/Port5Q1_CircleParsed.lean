import Port5Q1_CircleObservation
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_CircleParsed
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open AspisV8R19.DuplexFrames
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
open Port5Q1_QueryPorts
abbrev FE := OraclePortCheckpointAbiC5.E
abbrev FK := OraclePortCheckpointAbiC5.K

theorem folded (ops : Ops) (decoder : Port5Q1_OpeningValues.SessionAS3 ops)
    (comparison : Port5Q1_CircleObservation.SessionAComparison ops)
    (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : MatchingSupport.Data FE) (rho : FK) (prepare : SessionAPrepare p data q rho)
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some data)
    (wire : parsed.wire=bytesOf proof.val) (proofLength : proof.val.length=57607)
    (recovered : Nat → Option Bytes)
    (authenticated : ∀ pos, pos<22 → recovered (index q 2 pos)=
      some (OraclePortPackedChoiceC4.payload parsed 2 pos))
    (bound : a.next.val<22)
    (o : Port4C_QueryValues.Observation (Port4C_RowStd.install (install ops))
      proof p a out g obs geometry b bout) :
    CheckpointBytes5Output.ofE o.folded=data.V (q ⟨a.next.val,bound⟩) := by
  let j : Fin 22 := ⟨a.next.val,bound⟩
  have opening := Port5Q1_ObservedOpening.quartet ops decoder proof p a out g obs geometry b bout parsed q tr data
    read wire proofLength recovered authenticated j rfl o
  obtain ⟨actual,run,contents⟩ := WP.spec_imp_exists (Array.index_usize_spec p.queries a.next
    (by change a.next.val<p.queries.val.length; rw [p.queries.property]; exact bound))
  have same : actual=o.query := Result.ok.inj (run.symm.trans o.query_read)
  have raw : Port5Q1_GeometryBinding.queryAt p.queries a.next.val=o.query := by
    unfold Port5Q1_GeometryBinding.queryAt
    rw [List.getElem?_eq_getElem (by rw [p.queries.property]; exact bound),Option.getD_some]
    exact contents.symm.trans same
  have installedComparison : Port5Q1_CircleObservation.SessionAComparison (Port4C_RowStd.install (install ops)) :=
    ⟨comparison.unequal⟩
  exact Port5Q1_CircleObservation.selected (Port4C_RowStd.install (install ops)) installedComparison proof p a out
    g obs geometry b bout o (q j) data.V (by rw [←raw]; exact prepare.queries _ bound) opening.2

#print axioms folded
end AspisR1.Port5Q1_CircleParsed
end
