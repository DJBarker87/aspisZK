import NGW_ArrayLens
import NGW_ConstructorQM
set_option autoImplicit false
namespace NGW_FactorWrite
open Aeneas Aeneas.Std Result NGW_ConstructorQM NGW_ConstructorArrays
abbrev Row := Array Q 4#usize
abbrev Plane := Array Row 5#usize
abbrev Factors := Array Plane 5#usize
def CanonRow (row : Row) : Prop := Holds Canon row
def CanonPlane (plane : Plane) : Prop := Holds CanonRow plane
def CanonFactors (factors : Factors) : Prop := Holds CanonPlane factors

def write (f : Factors) (k d : Usize) (row : Row) : Result Factors := do
 let (plane,back) ← Array.index_mut_usize f k
 let out ← Array.update plane d row
 ok (back out)

theorem total (f : Factors) (k d : Usize) (row : Row) (hk : k.val<5) (hd : d.val<5)
 (hf : CanonFactors f) (hr : CanonRow row) :
 ∃ out,write f k d row=ok out ∧ CanonFactors out := by
 let plane := NGM_GuardExact.pick f k.val hk
 let next := put plane d.val row
 have cp := canonical_pick CanonPlane f k.val hk hf
 have cn := canonical_put CanonRow plane d.val row cp hr
 let out := put f k.val next
 have co := canonical_put CanonPlane f k.val next hf cn
 refine ⟨out,?_,co⟩
 simp only [write,NGW_ArrayLens.mutable f k hk,bind_tc_ok]
 dsimp! only
 rw [NGW_ConstructorArrays.update plane d row hd]
 rfl

#print axioms total
end NGW_FactorWrite
