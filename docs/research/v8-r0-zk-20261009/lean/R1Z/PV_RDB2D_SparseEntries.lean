import R1Z.PV_RDB2D_SparseFold
namespace R1Z.PV_RDB2D_SparseEntries
open PV_RDB2D_SparseAddress
set_option autoImplicit false

def entries {K : Type} (width trailing suffix : Nat) (weight : Nat → K) : List (Nat × K) :=
  (List.range (2^width)).map (fun pref => (row pref trailing suffix,weight pref))

theorem length {K : Type} (width trailing suffix : Nat) (weight : Nat → K) :
    (entries width trailing suffix weight).length=2^width := by simp only [entries,List.length_map,List.length_range]

theorem rows_bounded {K : Type} (width trailing suffix : Nat) (weight : Nat → K)
    (split : width+trailing=10) (hs : suffix<2^trailing) :
    ∀ entry ∈ entries width trailing suffix weight, entry.1<1024 := by
  intro entry h
  obtain ⟨pref,hp,rfl⟩ := List.mem_map.mp h
  exact bound width trailing suffix pref split hs (List.mem_range.mp hp)

#print axioms length
#print axioms rows_bounded
end R1Z.PV_RDB2D_SparseEntries
