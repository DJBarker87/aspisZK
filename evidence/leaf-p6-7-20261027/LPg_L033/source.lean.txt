import XRk_DecodeModels
import LPa_MonadicFold
open Aeneas Aeneas.Std Result
open XRk_Release
set_option autoImplicit false
namespace LPa.Boundary
-- Native stage bridge: r1_semantic::LPa_semantic::LPa_boundary (K016).
-- First coefficient is the seed AND the first loop value: it is counted twice.
def loop (p : Array aspis_core.field.QM31 28#usize) : Result aspis_core.field.QM31 := do
  let initial ← Array.index_usize p 0#usize
  LPa.walkM aspis_core.field.QM31.add p.val initial

theorem loop_eq_model (p : Array aspis_core.field.QM31 28#usize) :
    loop p = r1_semantic.semantic_boundary p := by
  simp only [loop, LPa.walkM_fold]
  rfl

theorem loop_eq_fold (p : Array aspis_core.field.QM31 28#usize) :
    loop p = (do
      let initial ← Array.index_usize p 0#usize
      p.val.foldlM aspis_core.field.QM31.add initial) := by
  simp only [loop, LPa.walkM_fold]

-- The actual bound is part of the carrier, rather than a new caller premise.
theorem actual_bound (p : Array aspis_core.field.QM31 28#usize) :
    p.val.length = 28 := p.property
#print axioms loop_eq_model
#print axioms loop_eq_fold
#print axioms actual_bound
end LPa.Boundary
