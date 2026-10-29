import R1Z.PV_RunJoin_WeightCoefficient46
import R1Z.PV_RunJoin_ArrayEntries41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CoefficientActualCell50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Column := Array W 1024#usize

def fallback (q : Column) : W := q.val[0]'(by rw [q.property];decide)
def permuted (q : Column) : Column := ProverCommitArray49.array 1024#usize
  (fun j => PV_RunJoin_ArrayEntries41.entries q (fallback q) (AspisR1.rowNat j))

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (q : Column) :
    @transport.Variant.coefficients (types base) (selected base heap box ops) W
      (@aspis_core.field.wide_exact.WideExact.Insts.CoreMarkerCopy (types base) (selected base heap box ops)) .S2 q=
        ok (permuted q) := by
  have h := PV_RunJoin_WeightCoefficient46.complete base heap box ops
    (@aspis_core.field.wide_exact.WideExact.Insts.CoreMarkerCopy (types base) (selected base heap box ops))
    (PV_RunJoin_ArrayEntries41.entries q (fallback q))
  rw [PV_RunJoin_ArrayEntries41.rebuild] at h
  exact h
#print axioms fallback
#print axioms permuted
#print axioms complete
end R1Z.PV_RunJoin_CoefficientActualCell50
