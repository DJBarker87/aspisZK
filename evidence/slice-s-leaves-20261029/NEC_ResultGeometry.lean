import Aeneas
set_option autoImplicit false
namespace NEC_ResultGeometry

def start (part : Fin 4) : Nat := match part.val with | 0=>8 | 1=>40 | 2=>72 | _=>104

def width (part : Fin 4) : Nat := if part.val<3 then 32 else 688

theorem header : 8≤792 := by omega

theorem copied_bounds (part : Fin 4) : start part+width part≤792 := by
 rcases part with ⟨part,bound⟩
 unfold start width
 have alternatives : part=0 ∨ part=1 ∨ part=2 ∨ part=3 := by omega
 rcases alternatives with h|h|h|h <;> subst part <;> simp

theorem copied_disjoint (left right : Fin 4) (ordered : left.val<right.val) :
 start left+width left≤start right := by
 rcases left with ⟨left,leftBound⟩
 rcases right with ⟨right,rightBound⟩
 unfold start width
 have leftCases : left=0 ∨ left=1 ∨ left=2 ∨ left=3 := by omega
 have rightCases : right=0 ∨ right=1 ∨ right=2 ∨ right=3 := by omega
 rcases leftCases with h|h|h|h <;> rcases rightCases with g|g|g|g <;> subst left <;> subst right <;> simp_all

theorem exact_afterstate_width : 792-104=688 := rfl

theorem arbitrary_byte {α : Type} (bytes : List α) (length : bytes.length=792)
 (part : Fin 4) (offset : Nat) (inside : offset<width part) : start part+offset<bytes.length := by
 have bound := copied_bounds part
 omega

#print axioms header
#print axioms copied_bounds
#print axioms copied_disjoint
#print axioms exact_afterstate_width
#print axioms arbitrary_byte
end NEC_ResultGeometry
