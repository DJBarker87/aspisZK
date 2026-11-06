import NKB_IndexFold

set_option autoImplicit false
namespace NKB_StrictCount
open AspisR1 MultiproofConeLiveLeaves

/-- Distinct ascending indices never take the duplicate branch. -/
theorem build_count (xs : List Nat) (k : Nat → Nat) (d : Nat)
    (ordered : xs.Pairwise (·<·))
    (future : ∀ a,a<d → ∀ x∈xs,k a<x) :
 (build xs k d).2=d+xs.length := by
 induction xs generalizing k d with
 | nil => simp only [build,List.length_nil,Nat.add_zero]
 | cons x xs ih =>
   obtain ⟨head,tail⟩ := List.pairwise_cons.mp ordered
   have fresh : ¬(0<d ∧ k (d-1)=x) := by
     rintro ⟨positive,same⟩
     have less := future (d-1) (by omega) x (by simp)
     omega
   have inserted : MultiproofConeLiveLeaves.insert k d x=
       ((fun j => if j=d then x else k j),d+1) := by
     simp only [MultiproofConeLiveLeaves.insert,if_neg fresh]
   have next : ∀ a,a<d+1 → ∀ y∈xs,(if a=d then x else k a)<y := by
     intro a ha y hy
     by_cases same : a=d
     · simp only [if_pos same];exact head y hy
     · simp only [if_neg same];exact future a (by omega) y (by simp only [List.mem_cons];exact Or.inr hy)
   have result := ih (fun j => if j=d then x else k j) (d+1) tail next
   simp only [build,inserted,List.length_cons]
   omega

/-- The actual TX2 C1/C2 sub-batch can contain twelve distinct canonical
indices. This list is queries[10..22] for queries[i]=i. -/
def tx2Indices : List Nat := (List.range 12).map (fun j => 10+j)

theorem ordered : tx2Indices.Pairwise (·<·) := by
 apply List.pairwise_iff_getElem.mpr
 intro i j hi hj less
 simp only [tx2Indices,List.getElem_map,List.getElem_range]
 omega

theorem canonical : ∀ x∈tx2Indices,x<262144 := by
 intro x member
 obtain ⟨j,hj,rfl⟩ := List.mem_map.mp member
 have bound := List.mem_range.mp hj
 omega

theorem twelve (k : Nat → Nat) : (build tx2Indices k 0).2=12 := by
 rw [build_count tx2Indices k 0 ordered (by intro a impossible;omega)]
 simp only [tx2Indices,List.length_map,List.length_range,Nat.zero_add]

/-- A required <=10 unit clause is false on this valid twelve-index producer.
This is a domain finding, not a shipped verifier failure or a security bound. -/
theorem not_ten (k : Nat → Nat) : ¬(build tx2Indices k 0).2≤10 := by
 rw [twelve k]
 omega

#print axioms build_count
#print axioms ordered
#print axioms canonical
#print axioms twelve
#print axioms not_ten
end NKB_StrictCount
