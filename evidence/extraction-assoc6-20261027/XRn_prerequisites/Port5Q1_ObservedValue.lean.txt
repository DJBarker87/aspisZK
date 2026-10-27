import Port5Q1_ObservedOpening
import Port5Q1_ObservedGeometry
import Port5Q1_LineInputs
import Port5Q1_InstallPorts
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_ObservedValue
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open AspisV8R19.DuplexFrames
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
open Port5Q1_QueryPorts
abbrev FE := OraclePortCheckpointAbiC5.E
abbrev FK := OraclePortCheckpointAbiC5.K
attribute [local irreducible] Port5Q1_Domain.lineZ FoldGeometryBridge.lz FoldGeometryBridge.lx FoldGeometryBridge.ly
  AspisV5FriReleasedLineGeometry.storedLine16X QueryResidualBridge.values QueryResidualBridge.basis

theorem value (ops : Ops) (ports : SessionAPrimitives ops)
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
    CheckpointBytes5Output.ofE o.value=QueryAccumulator.extend22 (QueryResidualBridge.values data q) a.next.val := by
  have bound : a.next.val<22 := Nat.lt_of_lt_of_le hi geo.bound
  let j : Fin 22 := ⟨a.next.val,bound⟩
  have rawEq : (Port5Q1_GeometryBinding.queryAt p.queries a.next.val).val=(q j).val := prepare.queries _ bound
  obtain ⟨opening,quartet⟩ := Port5Q1_ObservedOpening.quartet ops ports.decoder proof p a out g obs geometry b bout
    parsed q tr data read wire proofLength recovered authenticated j rfl o
  obtain ⟨zMeaning,ix,iy,iz⟩ := Port5Q1_ObservedGeometry.inputs ops ports proof p a out g obs geometry b bout
    data q rho prepare start end1 geo lo hi o
  have localPorts := Port5Q1_InstallPorts.rows ops ports
  have value := Port5Q1_LineInputs.value (Port4C_RowStd.install (install ops)) localPorts
    o.alpha1 o.value o.values o.inverse data (q j) (prepare.alpha1 _ o.alpha1_read) quartet ix iy iz o.line
  have jmod : (⟨a.next.val%22,Nat.mod_lt _ (by decide)⟩ : Fin 22)=j := Fin.ext (Nat.mod_eq_of_lt bound)
  exact ⟨opening,by simpa only [QueryAccumulator.extend22,jmod,QueryResidualBridge.values] using value⟩

#print axioms value
end AspisR1.Port5Q1_ObservedValue
end
