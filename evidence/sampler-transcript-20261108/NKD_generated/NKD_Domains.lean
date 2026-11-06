import NGT_RuntimeDomain
import NKD_New
set_option autoImplicit false
namespace AspisR1.NKD_Domains
/-- The native transcript packet covers every query/prepare payload through8192. -/
theorem absorb (state tag length payload size : Nat) (bound : size ≤ 8192) :
 (NGT_RuntimeDomain.absorbViews state tag length payload size).length ≤ 9 ∧
 ∀ v ∈ NGT_RuntimeDomain.absorbViews state tag length payload size, v.2 ≤ 57607 := by
 constructor
 · change 4 ≤ 9; decide
 · intro v member
   simp only [NGT_RuntimeDomain.absorbViews,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl <;> dsimp <;> omega
/-- Constructor descriptors fit the same CLOSED runtime forwarding packet. -/
theorem new (domain tag semantic : Nat) :
 ([(domain,29),(tag,1),(semantic,32)] : List (Nat×Nat)).length ≤ 9 ∧
 ∀ v ∈ ([(domain,29),(tag,1),(semantic,32)] : List (Nat×Nat)), v.2 ≤ 57607 := by
 constructor
 · change 3 ≤ 9; decide
 · intro v member
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl <;> dsimp <;> omega
/-- Valid disjoint native shared borrows preserve every payload byte over local log writes. -/
theorem frame {A : Type} (memory : Nat→A) (views : List NGT_RuntimeDomain.View)
 (writes : List (Nat×A))
 (disjoint : ∀ v∈views,∀ w∈writes,w.1<v.1 ∨ v.1+v.2≤w.1) :
 NFW_ImmutableIO.parts (NFW_ImmutableIO.writes memory writes) views =
 NFW_ImmutableIO.parts memory views := NGT_RuntimeDomain.input_frame memory views writes disjoint
#print axioms absorb
#print axioms new
#print axioms frame
end AspisR1.NKD_Domains
