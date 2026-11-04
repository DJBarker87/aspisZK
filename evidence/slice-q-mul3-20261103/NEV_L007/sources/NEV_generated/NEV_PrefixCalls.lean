import NEV_PrefixAssembly
set_option autoImplicit false
noncomputable section
namespace NEV_PrefixCalls
open Aeneas Aeneas.Std Result AspisR1

/-- The only product in the actual emitted iteration takes these SAME two
raw M31 words; canonicality of a previous product is not a precondition. -/
theorem m31_site (flat : Slice U32) (index : Usize) (product : U32)
    (inside : index.val<flat.val.length) :
    ∃ reply,
      NEI_LineFull.aspis_core.field.M31.mul product flat.val[index.val] = ok reply ∧
      NEG_PrefixFull.aspis_core.field.M31.mul product flat.val[index.val] = ok reply ∧
      reply.val=(product.val*(flat.val[index.val]'inside).val)%2147483647 ∧
      reply.val<2147483647 := by
  exact NEI_PrefixProduct.actual product flat.val[index.val]

def family : List Nat := (List.range 22).map (fun i => 5*(i+1))

/-- Finite native capacity coverage is precisely the reached family; this
does not assume a universal native theorem from a single diagnostic case. -/
theorem member (capacity : Nat) (positive : 0<capacity)
    (bound : capacity≤110) (multiple : capacity%5=0) : capacity∈family := by
  apply List.mem_map.mpr
  refine ⟨capacity/5-1,List.mem_range.mpr (by omega),?_⟩
  omega

theorem cases {P : Nat → Prop} (checked : ∀ c∈family,P c)
    (capacity : Nat) (positive : 0<capacity) (bound : capacity≤110)
    (multiple : capacity%5=0) : P capacity :=
  checked capacity (member capacity positive bound multiple)

#print axioms m31_site
#print axioms member
#print axioms cases
#print axioms NEG_PrefixAssociation.step
end NEV_PrefixCalls
end
