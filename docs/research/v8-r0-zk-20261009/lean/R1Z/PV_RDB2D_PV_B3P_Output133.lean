import R1Z.PV_RDB2D_PV_B3P_Install133
namespace PV_B3P_Output133
open Aeneas Aeneas.Std Result ProverRwFull
set_option autoImplicit false

-- The native carrier map preserves every element, not just success.
theorem toVec_val (r : Array U16 214#usize) :
    (PV_B3P_Install133.toVec r).val = r.val := rfl

theorem value_length : PV_B3P_Install133.value.val.length = 214 :=
  PV_B3P_Law133.length

theorem nonvacuity (base : ExternalTypes) (ops : @ExternalFuns base) :
    ∃ rows : alloc.vec.Vec U16,
      @ExternalFuns.op133 base (PV_B3P_Install133.selected base ops) = ok (.Ok rows) ∧
      rows.val.length = 214 :=
  ⟨_, PV_B3P_Install133.source base ops, value_length⟩

#print axioms toVec_val
#print axioms value_length
#print axioms nonvacuity
end PV_B3P_Output133
