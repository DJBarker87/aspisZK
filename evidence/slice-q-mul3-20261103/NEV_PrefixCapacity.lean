import NEV_PrefixAssembly
set_option autoImplicit false
namespace NEV_PrefixCapacity

/-- Every live prefix at every legal requested capacity has an exact-capacity
value representative. No constraint is imposed on a live word. Physical
uninitialised-spare transport remains part of the native association review. -/
theorem representative {T : Type} (before : List T) (filler : T) (capacity : Nat)
    (room : before.length < capacity) :
    ∃ storage : List T, storage.length = capacity ∧
      storage.take before.length = before := by
  refine ⟨before ++ List.replicate (capacity-before.length) filler,?_,?_⟩
  · simp only [List.length_append,List.length_replicate]
    omega
  · simp

/-- Capacity zero never reaches a push. A finite interval cover is sufficient
only when every nonzero capacity through the actual maximum is proved. -/
theorem partition {P : Nat → Prop}
    (low : ∀ c, 1≤c → c≤16 → P c)
    (b1 : ∀ c, 17≤c → c≤32 → P c)
    (b2 : ∀ c, 33≤c → c≤48 → P c)
    (b3 : ∀ c, 49≤c → c≤64 → P c)
    (b4 : ∀ c, 65≤c → c≤80 → P c)
    (b5 : ∀ c, 81≤c → c≤96 → P c)
    (high : ∀ c, 97≤c → c≤110 → P c)
    (capacity index : Nat) (bounded : capacity≤110) (active : index<capacity) : P capacity := by
  by_cases h0 : capacity≤16
  · exact low capacity (by omega) h0
  by_cases h1 : capacity≤32
  · exact b1 capacity (by omega) h1
  by_cases h2 : capacity≤48
  · exact b2 capacity (by omega) h2
  by_cases h3 : capacity≤64
  · exact b3 capacity (by omega) h3
  by_cases h4 : capacity≤80
  · exact b4 capacity (by omega) h4
  by_cases h5 : capacity≤96
  · exact b5 capacity (by omega) h5
  exact high capacity (by omega) bounded

#print axioms representative
#print axioms partition
end NEV_PrefixCapacity
