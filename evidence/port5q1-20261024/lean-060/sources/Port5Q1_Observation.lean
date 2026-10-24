import Port5Q1_ObservedOpening
import Port5Q1_LineInputs
import Port5Q1_InstallPorts
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
  have bound : a.next.val<22 := Nat.lt_of_lt_of_le hi geo.bound
  let j : Fin 22 := ⟨a.next.val,bound⟩
  have rawEq : (Port5Q1_GeometryBinding.queryAt p.queries a.next.val).val=(q j).val := prepare.queries _ bound
  obtain ⟨opening,quartet⟩ := Port5Q1_ObservedOpening.quartet ops ports.decoder proof p a out g obs geometry b bout
    parsed q tr data read wire proofLength recovered authenticated j rfl o
  have geometric := Port5Q1_GeometryAccessor.reads p.queries start end1 geometry geo a.next lo hi
    o.inverse o.z o.inverse_read o.z_read
  have ix : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 2)=
      (FoldGeometryBridge.lx (Port5Q1_Domain.parent (q j).val))⁻¹ := by
    have h := geometric.2 (2 : Fin 5)
    simpa only [Port5Q1_Domain.words,rawEq,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] using h
  have iy : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 3)=
      (FoldGeometryBridge.ly (Port5Q1_Domain.parent (q j).val))⁻¹ := by
    have h := geometric.2 (3 : Fin 5)
    simpa only [Port5Q1_Domain.words,rawEq,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] using h
  have iz : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 4)=
      (FoldGeometryBridge.lz (Port5Q1_Domain.parent (q j).val))⁻¹ := by
    have h := geometric.2 (4 : Fin 5)
    simpa only [Port5Q1_Domain.words,Port5Q1_Domain.lineZ,rawEq,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] using h
  have localPorts := Port5Q1_InstallPorts.rows ops ports
  have value := Port5Q1_LineInputs.value (Port4C_RowStd.install (install ops)) localPorts
    o.alpha1 o.value o.values o.inverse data (q j) (prepare.alpha1 _ o.alpha1_read) quartet ix iy iz o.line
  have parentEq : Port5Q1_Domain.parent (q j).val=AspisR1.parentIndex (n:=65536) (q j) := by
    apply Fin.ext
    change (q j).val/4%65536=(q j).val/4
    apply Nat.mod_eq_of_lt
    have := (q j).isLt
    omega
  have zMeaning : S7JoinBasisMachine.decode o.z=FoldGeometryBridge.lz (Port5Q1_Domain.parent (q j).val) := by
    simpa only [rawEq,Port5Q1_Domain.lineZ] using geometric.1
  have node := Port5Q1_NodeModel.node (Port4C_RowStd.install (install ops)) localPorts.m31
    _ o.z o.square o.doubled o.one o.node zMeaning o.square_call o.double_call o.one_call o.node_call
  rw [parentEq] at node
  have jmod : (⟨a.next.val%22,Nat.mod_lt _ (by decide)⟩ : Fin 22)=j := Fin.ext (Nat.mod_eq_of_lt bound)
  refine ⟨opening,?_,?_⟩
  · simpa only [QueryAccumulator.extend22,jmod,QueryResidualBridge.values] using value
  · intro i
    simpa only [QueryAccumulator.extend22,jmod] using Port5Q1_NodeModel.basis q j o.node node i

#print axioms fields
end AspisR1.Port5Q1_Observation
end
