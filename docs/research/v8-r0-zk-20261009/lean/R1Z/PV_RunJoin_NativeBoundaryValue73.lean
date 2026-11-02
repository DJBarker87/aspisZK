import R1Z.PV_RunJoin_BoundaryFinish73
import R1Z.PV_RunJoin_BoundaryPolynomial73
import R1Z.PV_RunJoin_NativeSumcheckArithmetic72
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeBoundaryValue73
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
open PV_RunJoin_FieldData34 (value canonical)
open PV_RunJoin_AccPolynomial38 (poly)
abbrev Q := aspis_core.field.QM31

theorem source (p : Nat → Q) :
    ∃ q,ProverRwP6BoundarySource.boundary_flat (PV_RunJoin_MergeArray35.array p)=ok q ∧
      canonical q ∧ value q=(poly p).eval 0+(poly p).eval 1 := by
  obtain ⟨q,hq,hc,ha,hb,hcc,hd⟩ := PV_RunJoin_BoundaryFinish73.complete
    (PV_RunJoin_BoundaryFold73.fold p 27 1 (PV_RunJoin_BoundaryFold73.initial (p 0)))
  obtain ⟨va,vb,vc,vd⟩ := PV_RunJoin_BoundaryFold73.values p 27 1 2
    (PV_RunJoin_BoundaryFold73.initial (p 0)) (by decide)
    (PV_RunJoin_BoundaryFold73.initial_bound (p 0))
  obtain ⟨ia,ib,ic,id⟩ := PV_RunJoin_BoundaryFold73.initial_values (p 0)
  rw [va,ia] at ha
  rw [vb,ib] at hb
  rw [vc,ic] at hcc
  rw [vd,id] at hd
  refine ⟨q,by rw [PV_RunJoin_BoundarySource73.complete];exact hq,hc,?_⟩
  rw [←PV_RunJoin_BoundaryPolynomial73.polynomial_boundary p]
  apply PV_RunJoin_BoundaryPolynomial73.output_value p q
  intro k
  fin_cases k
  · exact ha
  · exact hb
  · exact hcc
  · exact hd

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (p : Nat → Q) :
    ∃ q,@aspis_core.state_only_sumcheck.state_only_boundary_sum (types base)
      (opsNative base heap box ops runtime world) (PV_RunJoin_MergeArray35.array p)=ok q ∧
      canonical q ∧ value q=(poly p).eval 0+(poly p).eval 1 := by
  rw [PV_RunJoin_NativeSumcheckArithmetic72.boundary_source]
  exact source p

#print axioms source
#print axioms complete
end R1Z.PV_RunJoin_NativeBoundaryValue73
