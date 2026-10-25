import Port6CK_Advance
import Port5Q1_Observation
import OraclePortCheckpointResumeC5
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_Binding
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open AspisV8R19.DuplexFrames
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
open Port5Q1_QueryPorts
abbrev FE := OraclePortCheckpointAbiC5.E
abbrev FK := OraclePortCheckpointAbiC5.K
attribute [local irreducible] QueryResidualBridge.values QueryResidualBridge.basis

/-- Q1's retained authenticated premise is unchanged. Geometry bounds are
explicit on the observation, rather than asserted for arbitrary accumulator
indices as in Q2's original universal interface. -/
theorem from_observation (ops : Ops) (ports : SessionAPrimitives ops)
    (proof : Slice U8) (p : verifier.Prepared)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : MatchingSupport.Data FE) (rho : FK)
    (prepare : SessionAPrepare p data q rho)
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some data)
    (wire : parsed.wire=bytesOf proof.val) (proofLength : proof.val.length=57607)
    (recovered : Nat → Option Bytes)
    (authenticated : ∀ pos, pos<22 → recovered (index q 2 pos)=
      some (OraclePortPackedChoiceC4.payload parsed 2 pos))
    (start end1 : Usize) (geo : Port5Q1_GeometryBinding.Binding p.queries start end1 geometry)
 :
    Port6CK_Advance.ObservationBinding (install ops) proof p g obs geometry
      (OraclePortCheckpointResumeC5.model data rho q) start.val end1.val := by
  refine ⟨rfl,prepare.rho_eq.symm,?_,?_⟩
  · intro a out b bout o lo hi
    exact (Port5Q1_Observation.fields ops ports proof p a out g obs geometry b bout
      parsed q tr data rho prepare read wire proofLength recovered authenticated start end1 geo lo hi o).2.1
  · intro a out b bout o i lo hi
    exact (Port5Q1_Observation.fields ops ports proof p a out g obs geometry b bout
      parsed q tr data rho prepare read wire proofLength recovered authenticated start end1 geo lo hi o).2.2 i

#print axioms from_observation
end AspisR1.Port6CK_Binding
end
