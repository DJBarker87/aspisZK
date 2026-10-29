import R1Z.PV_RDB2D_SparseFold
namespace R1Z.PV_RDB2D_SparseFieldOrder
open Aeneas Aeneas.Std Result PV_RDB2D_SparseFold
set_option autoImplicit false

theorem ordered_calls {K : Type} (ops : Ops K) (column : List K) (row : Nat) (weight sum value : K)
    (h : PV_RDB2D_SparseLookup.read column row=ok value) :
    term ops column sum (row,weight)=(do let product ← ops.mul weight value; ops.add sum product) := by
  simp only [term,h,bind_tc_ok]

theorem no_add_after_mul_failure {K : Type} (ops : Ops K) (column : List K)
    (row : Nat) (weight sum value : K) (e : Error)
    (read : PV_RDB2D_SparseLookup.read column row=ok value) (mul : ops.mul weight value=fail e) :
    term ops column sum (row,weight)=fail e := by
  rw [ordered_calls ops column row weight sum value read,mul]
  simp only [bind_tc_fail]

#print axioms ordered_calls
#print axioms no_add_after_mul_failure
end R1Z.PV_RDB2D_SparseFieldOrder
