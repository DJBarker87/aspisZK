import XRu_RowShape
open Aeneas Aeneas.Std Result ControlFlow XRn_Join_Release
set_option autoImplicit false
namespace XRu_RowStep
open XRu_RowShape
/-- A reached emitted row update uses these exact scalar operations and set. -/
theorem source (row : Row) (limbs : Limbs) (basis : U32) (i j : Usize)
 (lt : i.val<4) (inc : j.val=i.val+1) :
 verifier.update_residue_row_loop0.body limbs {start:=i,«end»:=4#usize} row basis =
 (do
  let old ← Array.index_usize row i
  let limb ← Array.index_usize limbs i
  let product ← (core.convert.num.FromU64U32.from limb) * (core.convert.num.FromU64U32.from basis)
  let sum ← old + product
  let out ← Array.update row i sum
  ok (cont ({start:=j,«end»:=4#usize},out,basis))) := by
 unfold verifier.update_residue_row_loop0.body
 rw [range i j lt inc]
 rfl
#print axioms source
end XRu_RowStep
