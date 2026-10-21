import AllocationBatchM10

/-! Closed form for a uniform constructor schedule. Never build millions of
identical counter cells merely to add the same fixed tariff. -/
set_option autoImplicit false
namespace AspisR1.AllocationBatchConstantM10

theorem cells (n C : Nat) :
    AllocationBatchM10.cells (fun _ : Fin n => C) = n*C+3*n+1 := by
  simp only [AllocationBatchM10.cells,List.ofFn_const,List.sum_replicate,nsmul_eq_mul]
  rfl

#print axioms cells
end AspisR1.AllocationBatchConstantM10
