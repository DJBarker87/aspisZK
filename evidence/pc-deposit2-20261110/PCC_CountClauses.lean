import PCC_BasicReferences
set_option autoImplicit false
namespace PCC
open PCA
/-- Exhaustive count split required by (c-c). No fixed account bound. -/
theorem count_reply (expected : Nat) (s : PCA_State) :
    (countReference expected s).reply =
      if s.accountCount = expected then .ok ()
      else if s.accountCount < expected then .error (.program notEnoughKeys)
      else .error (.program (2*2^32)) := by
  by_cases he : s.accountCount = expected
  · simp only [countReference,PCA.countReference,he,↓reduceIte]
  · by_cases hl : s.accountCount < expected <;> simp only [countReference,PCA.countReference,he,hl,↓reduceIte]

theorem count_success (expected : Nat) (s : PCA_State)
    (h : (countReference expected s).reply = .ok ()) : s.accountCount = expected := by
  by_contra ne
  rw [count_reply,if_neg ne] at h
  split at h <;> cases h
#print axioms count_reply
#print axioms count_success
end PCC
