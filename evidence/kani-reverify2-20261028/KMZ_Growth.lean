import KMY_RootComposition
set_option autoImplicit false
namespace KMZ_Growth
open KMX_CopyMeaning KMY_WindowComposition
/-- Value composition only. Successful allocation and the actual heap association
are Rust obligations; this theorem does not replace those gates. -/
theorem append_after_growth (before garbage source : Nat → Nat)
    (len oldCap newCap size j : Nat) (live : len ≤ oldCap)
    (growth : oldCap ≤ newCap) (bound : j < len+size) :
    window source (loop before garbage 0 (min oldCap newCap)) len size j =
      if j<len then before j else source (j-len) := by
  rw [KMY_SerializerComposition.append_window _ _ len size j bound]
  by_cases h : j<len
  · simp only [if_pos h]
    exact KMY_VectorComposition.growth_retains before garbage oldCap newCap j growth (by omega)
  · simp only [if_neg h]
#print axioms append_after_growth
end KMZ_Growth
