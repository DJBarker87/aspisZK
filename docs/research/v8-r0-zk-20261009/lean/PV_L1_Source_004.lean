import PV_L1_ResultCoercion
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_004
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (queries : Array Std.U32 22#usize) (begin1 : Std.Usize) (end1 : Std.Usize)
  (folded : Bool) :
  Logged (alloc.vec.Vec Std.U32)
  := do
  let _ ← observe .publication 0 (ok ())
  let i ← PV_L1_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_sub end1 begin1))
  let out := alloc.vec.Vec.with_capacity Std.U32 i
  prover.publication_indices_loop0 queries end1 folded out begin1

theorem complete_result
  (queries : Array Std.U32 22#usize) (begin1 : Std.Usize) (end1 : Std.Usize)
  (folded : Bool) :
  erase (produce queries begin1 end1 folded) = prover.publication_indices queries begin1 end1 folded := by
  unfold produce prover.publication_indices
  simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
#print axioms complete_result
end PV_L1_Source_004
