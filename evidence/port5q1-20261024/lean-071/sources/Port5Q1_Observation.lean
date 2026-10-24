import Port5Q1_ObservedValue
import Port5Q1_ObservedBasis
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_Observation
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open AspisV8R19.DuplexFrames
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
open Port5Q1_QueryPorts
abbrev FE := OraclePortCheckpointAbiC5.E
abbrev FK := OraclePortCheckpointAbiC5.K
attribute [local irreducible] Port5Q1_Domain.lineZ FoldGeometryBridge.lz FoldGeometryBridge.lx FoldGeometryBridge.ly
  AspisV5FriReleasedLineGeometry.storedLine16X QueryResidualBridge.values QueryResidualBridge.basis

theorem fields (ops : Ops) (ports : SessionAPrimitives ops)
    (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : MatchingSupport.Data FE) (rho : FK)
    (prepare : SessionAPrepare p data q rho)
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some data)
    (wire : parsed.wire=bytesOf proof.val) (proofLength : proof.val.length=57607)
    (recovered : Nat → Option Bytes)
    (authenticated : ∀ pos, pos<22 → recovered (index q 2 pos)=
      some (OraclePortPackedChoiceC4.payload parsed 2 pos))
    (start end1 : Usize) (geo : Port5Q1_GeometryBinding.Binding p.queries start end1 geometry)
    (lo : start.val ≤ a.next.val) (hi : a.next.val<end1.val)
    (o : Port4C_QueryValues.Observation (Port4C_RowStd.install (install ops))
      proof p a out g obs geometry b bout) :
    bytesOf o.opening.val=opening parsed a.next.val ∧
    CheckpointBytes5Output.ofE o.value=QueryAccumulator.extend22 (QueryResidualBridge.values data q) a.next.val ∧
    (∀ i : Fin 64, Port4C_SumField.scalar
      (AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode o.node) i.val)=
      QueryAccumulator.extend22 (QueryResidualBridge.basis (K:=FK) q) a.next.val i) := by
  have value := Port5Q1_ObservedValue.value ops ports proof p a out g obs geometry b bout parsed q tr data rho
    prepare read wire proofLength recovered authenticated start end1 geo lo hi o
  exact ⟨value.1,value.2,Port5Q1_ObservedBasis.basis ops ports proof p a out g obs geometry b bout
    data q rho prepare start end1 geo lo hi o⟩

#print axioms fields
end AspisR1.Port5Q1_Observation
end
