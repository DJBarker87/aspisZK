import Port5Q1_Gather
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_GeometryModel
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeGeometryBody
variable {CoreError : Type}

/-- Full nonempty for_range field result, on the SAME accepted current
parent. Raw-zero exclusion and field nonzero are derived through gathering;
there is no independent successful prefix, inversion or collect premise. -/
theorem for_range (ops : Ops CoreError)
    (leaves : Port5Q1_GeometryCanonical.SessionAPrimitives ops)
    (domain : Port5Q1_Domain.SessionADomain ops)
    (multiply : ops.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : ops.op7=ok (1#u32))
    (inverseLeaf : ops.op11=Port4C_InverseExecution.inverse_owned)
    (queries : Array U32 22#usize) (start end1 : Usize) (out : verifier.QueryGeometry)
    (nonempty : start.val < end1.val)
    (accepted : Port3_GeometryStage.geometry (Port5Q1_GeometryTerminal.install ops)
      queries start end1=ok (.Ok out)) :
    ∃ flat inverse : alloc.vec.Vec U32,
      out.start=start ∧ out.line_z.val.length=end1.val-start.val ∧
      flat.val.length=5*(end1.val-start.val) ∧
      (∀ x ∈ flat.val, Port5Q1_GeometryCanonical.Canonical x) ∧
      (∀ x ∈ flat.val, S7JoinBasisMachine.decode x≠0) ∧
      inverse.val.length=flat.val.length ∧
      (∀ j, j<flat.val.length →
        S7JoinBasisMachine.decode (Port4C_BatchInverse.cell inverse.val j)=
          (S7JoinBasisMachine.decode (Port4C_BatchInverse.cell flat.val j))⁻¹) ∧
      out.inverses.val=(List.range (end1.val-start.val)).map (Port4C_CollectLoop.record inverse) ∧
      flat.val.map S7JoinBasisMachine.decode=
        ((queries.val.drop start.val).take (end1.val-start.val)).flatMap (fun q => Port5Q1_Domain.words q.val) ∧
      out.line_z.val.map S7JoinBasisMachine.decode=
        ((queries.val.drop start.val).take (end1.val-start.val)).map (fun q => Port5Q1_Domain.lineZ q.val) := by
  let installed := Port5Q1_GeometryTerminal.install ops
  obtain ⟨selected,order,bound,selection,run⟩ := Port4C_GeometryRange.accepted_range
    installed queries start end1 out accepted
  have selectedFields := Port4C_GeometryFields.selection_fields queries start end1 selected order bound selection
  have installedLeaves : Port5Q1_GeometryCanonical.SessionAPrimitives installed :=
    ⟨leaves.point,leaves.line,leaves.multiply,leaves.double,leaves.one,leaves.subtract⟩
  have installedDomain : Port5Q1_Domain.SessionADomain installed :=
    ⟨domain.fibre,domain.point,domain.line,domain.multiply,domain.double,domain.one,domain.subtract⟩
  obtain ⟨zs,flat,terminal,canon,raw,body,ending,zlen,flen,flatMeaning,lineMeaning⟩ :=
    Port5Q1_Gather.traversal installed installedLeaves installedDomain start ⟨selected,0⟩
      (alloc.vec.Vec.new U32) (alloc.vec.Vec.new U32) out selected.val.length
      (by simp) (by simp [alloc.vec.Vec.new]) (by simp [alloc.vec.Vec.new]) run
  have nz : ∀ x ∈ flat.val, S7JoinBasisMachine.decode x≠0 :=
    fun x member => Port5Q1_GeometryCanonical.field_nonzero x (canon x member) (raw x member)
  have hz : zs.val.length=end1.val-start.val := by
    simpa only [alloc.vec.Vec.new,List.length_nil,Nat.zero_add,selectedFields.2] using zlen
  have hf : flat.val.length=5*(end1.val-start.val) := by
    simpa only [alloc.vec.Vec.new,List.length_nil,Nat.zero_add,selectedFields.2] using flen
  obtain ⟨inverse,hs,hl,hi,values,groups⟩ := Port5Q1_GeometryTerminal.terminal ops multiply one inverseLeaf
    start terminal zs flat out ending (by omega) (by omega) (by omega) nz body
  refine ⟨flat,inverse,hs,hl ▸ hz,hf,canon,nz,hi,values,by simpa only [hz] using groups,?_,?_⟩
  · simpa only [alloc.vec.Vec.new,List.map_nil,List.drop_zero,List.nil_append,selectedFields.1] using flatMeaning
  · rw [hl]
    simpa only [alloc.vec.Vec.new,List.map_nil,List.drop_zero,List.nil_append,selectedFields.1] using lineMeaning

#print axioms for_range
end AspisR1.Port5Q1_GeometryModel
end
