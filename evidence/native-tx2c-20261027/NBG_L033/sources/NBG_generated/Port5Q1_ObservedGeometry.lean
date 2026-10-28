import Port5Q1_InstallPorts
import Port5Q1_DomainLanes
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_ObservedGeometry
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open AspisV8R19.DuplexFrames
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
open Port5Q1_QueryPorts
abbrev FE := OraclePortCheckpointAbiC5.E
abbrev FK := OraclePortCheckpointAbiC5.K
attribute [local irreducible] Port5Q1_Domain.words Port5Q1_Domain.lineZ FoldGeometryBridge.lz FoldGeometryBridge.lx FoldGeometryBridge.ly
  AspisV5FriReleasedLineGeometry.storedLine16X QueryResidualBridge.values QueryResidualBridge.basis

theorem inputs (ops : Ops) (ports : SessionAPrimitives ops)
    (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
    (data : MatchingSupport.Data FE) (q : Fin 22 → Fin 262144) (rho : FK)
    (prepare : SessionAPrepare p data q rho)
    (start end1 : Usize) (geo : Port5Q1_GeometryBinding.Binding p.queries start end1 geometry)
    (lo : start.val ≤ a.next.val) (hi : a.next.val<end1.val)
    (o : Port4C_QueryValues.Observation (Port4C_RowStd.install (install ops))
      proof p a out g obs geometry b bout) :
    let j : Fin 22 := ⟨a.next.val,Nat.lt_of_lt_of_le hi geo.bound⟩
    S7JoinBasisMachine.decode o.z=FoldGeometryBridge.lz (Port5Q1_Domain.parent (q j).val) ∧
    S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 2)=
      (FoldGeometryBridge.lx (Port5Q1_Domain.parent (q j).val))⁻¹ ∧
    S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 3)=
      (FoldGeometryBridge.ly (Port5Q1_Domain.parent (q j).val))⁻¹ ∧
    S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 4)=
      (FoldGeometryBridge.lz (Port5Q1_Domain.parent (q j).val))⁻¹ := by
  have bound : a.next.val<22 := Nat.lt_of_lt_of_le hi geo.bound
  let j : Fin 22 := ⟨a.next.val,bound⟩
  have rawEq : (Port5Q1_GeometryBinding.queryAt p.queries a.next.val).val=(q j).val := prepare.queries _ bound
  have geometric := Port5Q1_GeometryAccessor.reads p.queries start end1 geometry geo a.next lo hi
    o.inverse o.z o.inverse_read o.z_read
  have ix : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 2)=
      (FoldGeometryBridge.lx (Port5Q1_Domain.parent (q j).val))⁻¹ := by
    have h := geometric.2 (2 : Fin 5)
    change S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 2)=
      ((Port5Q1_Domain.words (Port5Q1_GeometryBinding.queryAt p.queries a.next.val).val)[2]?.getD 0)⁻¹ at h
    rw [rawEq,Port5Q1_DomainLanes.x] at h
    exact h
  have iy : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 3)=
      (FoldGeometryBridge.ly (Port5Q1_Domain.parent (q j).val))⁻¹ := by
    have h := geometric.2 (3 : Fin 5)
    change S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 3)=
      ((Port5Q1_Domain.words (Port5Q1_GeometryBinding.queryAt p.queries a.next.val).val)[3]?.getD 0)⁻¹ at h
    rw [rawEq,Port5Q1_DomainLanes.y] at h
    exact h
  have iz : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 4)=
      (FoldGeometryBridge.lz (Port5Q1_Domain.parent (q j).val))⁻¹ := by
    have h := geometric.2 (4 : Fin 5)
    change S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 4)=
      ((Port5Q1_Domain.words (Port5Q1_GeometryBinding.queryAt p.queries a.next.val).val)[4]?.getD 0)⁻¹ at h
    rw [rawEq,Port5Q1_DomainLanes.z] at h
    exact h
  have zMeaning : S7JoinBasisMachine.decode o.z=FoldGeometryBridge.lz (Port5Q1_Domain.parent (q j).val) := by
    simpa only [rawEq,Port5Q1_Domain.lineZ] using geometric.1
  exact ⟨zMeaning,ix,iy,iz⟩

#print axioms inputs
end AspisR1.Port5Q1_ObservedGeometry
end
