import Port5Q1_ObservedGeometry
import Port5Q1_InstallPorts
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_ObservedBasis
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open AspisV8R19.DuplexFrames
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
open Port5Q1_QueryPorts
abbrev FE := OraclePortCheckpointAbiC5.E
abbrev FK := OraclePortCheckpointAbiC5.K
attribute [local irreducible] Port5Q1_Domain.lineZ FoldGeometryBridge.lz FoldGeometryBridge.lx FoldGeometryBridge.ly
  AspisV5FriReleasedLineGeometry.storedLine16X QueryResidualBridge.values QueryResidualBridge.basis

theorem basis (ops : Ops) (ports : SessionAPrimitives ops)
    (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
    (data : MatchingSupport.Data FE) (q : Fin 22 → Fin 262144) (rho : FK)
    (prepare : SessionAPrepare p data q rho)
    (start end1 : Usize) (geo : Port5Q1_GeometryBinding.Binding p.queries start end1 geometry)
    (lo : start.val ≤ a.next.val) (hi : a.next.val<end1.val)
    (o : Port4C_QueryValues.Observation (Port4C_RowStd.install (install ops))
      proof p a out g obs geometry b bout) :
    ∀ i : Fin 64, Port4C_SumField.scalar
      (AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode o.node) i.val)=
      QueryAccumulator.extend22 (QueryResidualBridge.basis (K:=FK) q) a.next.val i := by
  have bound : a.next.val<22 := Nat.lt_of_lt_of_le hi geo.bound
  let j : Fin 22 := ⟨a.next.val,bound⟩
  have rawEq : (Port5Q1_GeometryBinding.queryAt p.queries a.next.val).val=(q j).val := prepare.queries _ bound
  have input := Port5Q1_ObservedGeometry.inputs ops ports proof p a out g obs geometry b bout
    data q rho prepare start end1 geo lo hi o
  have zMeaning := input.1
  have parentEq : Port5Q1_Domain.parent (q j).val=AspisR1.parentIndex (n:=65536) (q j) := by
    apply Fin.ext
    change (q j).val/4%65536=(q j).val/4
    apply Nat.mod_eq_of_lt
    have := (q j).isLt
    omega
  have node := Port5Q1_NodeModel.node (Port4C_RowStd.install (install ops)) (Port5Q1_InstallPorts.rows ops ports).m31
    _ o.z o.square o.doubled o.one o.node zMeaning o.square_call o.double_call o.one_call o.node_call
  rw [parentEq] at node
  have jmod : (⟨a.next.val%22,Nat.mod_lt _ (by decide)⟩ : Fin 22)=j := Fin.ext (Nat.mod_eq_of_lt bound)
  intro i
  simpa only [QueryAccumulator.extend22,jmod] using Port5Q1_NodeModel.basis q j o.node node i

#print axioms basis
end AspisR1.Port5Q1_ObservedBasis
end
