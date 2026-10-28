import KNA_Frame
set_option autoImplicit false
namespace KNA_LPi_K017
open KMX_CopyMeaning KMY_WindowComposition

def joinedPrefix (body hp hu : Nat → Nat) := window hu (window hp body 16 32) 48 32

theorem result (body garbage hp hu answer : Nat → Nat) (j : Nat) (bound : j<1768) :
 window answer (loop (joinedPrefix body hp hu) garbage 0 (min 1736 3472)) 1736 32 j =
 if 16≤j ∧ j<48 then hp (j-16) else if 48≤j ∧ j<80 then hu (j-48)
 else if j<1736 then body j else if j<1768 then answer (j-1736) else body j := by
 calc
  _ = (if j<1736 then joinedPrefix body hp hu j else answer (j-1736)) :=
   KMZ_Growth.append_after_growth _ garbage answer 1736 1736 3472 32 j (by omega) (by omega) (by omega)
  _ = window answer (joinedPrefix body hp hu) 1736 32 j :=
   (KMY_SerializerComposition.append_window answer (joinedPrefix body hp hu) 1736 32 j (by omega)).symm
  _ = _ := KMY_SerializerComposition.joined_digest body hp hu answer j
#print axioms result
end KNA_LPi_K017
