import KMZ_Growth
set_option autoImplicit false
namespace KMZ_LPe_K016
open KMX_CopyMeaning KMY_WindowComposition
/-- Compose the three retained-prefix reallocations, rather than treating
allocator growth as a byte-neutral operation without a proof. -/
def first (before garbage hp : Nat → Nat) :=
 window hp (loop before garbage 0 (min 16 48)) 16 32
def second (before garbage hp hu : Nat → Nat) :=
 window hu (loop (first before garbage hp) garbage 0 (min 48 96)) 48 32

theorem result (before garbage hp hu state : Nat → Nat) (j : Nat) (bound : j<112) :
 window state (loop (second before garbage hp hu) garbage 0 (min 96 192)) 80 32 j =
 if j<16 then before j else if j<48 then hp (j-16)
 else if j<80 then hu (j-48) else state (j-80) := by
 rw [KMZ_Growth.append_after_growth _ _ _ 80 96 192 32 j (by omega) (by omega) bound]
 by_cases h80 : j<80
 · rw [if_pos h80]
   unfold second
   rw [KMZ_Growth.append_after_growth _ _ _ 48 48 96 32 j (by omega) (by omega) (by omega)]
   by_cases h48 : j<48
   · rw [if_pos h48]
     unfold first
     rw [KMZ_Growth.append_after_growth _ _ _ 16 16 48 32 j (by omega) (by omega) (by omega)]
     by_cases h16 : j<16
     · simp only [if_pos h16]
     · simp only [if_neg h16, if_pos h48]
   · have h16 : ¬ j<16 := by omega
     simp only [if_neg h48, if_neg h16, if_pos h80]
 · have h16 : ¬ j<16 := by omega
   have h48 : ¬ j<48 := by omega
   simp only [if_neg h80, if_neg h16, if_neg h48]
#print axioms result
end KMZ_LPe_K016
