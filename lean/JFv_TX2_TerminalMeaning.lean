import JFv_TX2_Terminal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_TerminalMeaning
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeGeometryBody

theorem source {C : Type} (err : C) (seed : Ops C)
    (start : Usize) (it : core.slice.iter.Iter U32) (zs flat : alloc.vec.Vec U32)
    (ending : it.i=it.slice.val.length) (count : zs.val.length≤22)
    (size : flat.val.length=5*zs.val.length) (positive : 0<zs.val.length)
    (nonzero : ∀ x∈flat.val,S7JoinBasisMachine.decode x≠0) :
    ∃ (out : verifier.QueryGeometry) (inverse : alloc.vec.Vec U32),
      verifier.QueryGeometry.for_range_loop0.body (JFv_TX2_GeometryOps.install err seed)
        start it zs flat=ok (done (.Ok out)) ∧
      out.start=start ∧ out.line_z=zs ∧
      inverse.val.length=flat.val.length ∧
      (∀ j, j<flat.val.length →
        S7JoinBasisMachine.decode (Port4C_BatchInverse.cell inverse.val j)=
          (S7JoinBasisMachine.decode (Port4C_BatchInverse.cell flat.val j))⁻¹) ∧
      out.inverses.val=(List.range zs.val.length).map (Port4C_CollectLoop.record inverse) := by
  obtain ⟨out,run,_,_,_⟩ := JFv_TX2_Terminal.source err seed start it zs flat
    ending count size positive nonzero
  obtain ⟨inverse,hs,hl,hi,values,groups⟩ := Port5Q1_GeometryTerminal.terminal
    (SAQ_Constructor.install err seed) rfl rfl SAQ_Inverse.source_eq_reference
    start it zs flat out ending count size positive nonzero run
  exact ⟨out,inverse,run,hs,hl,hi,values,groups⟩
#print axioms source
end AspisR1.JFv_TX2_TerminalMeaning
end
