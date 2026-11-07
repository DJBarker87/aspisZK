import NDB_DigestReject
import NMX_R3_DigestPositive
set_option autoImplicit false
namespace NMX_R3_DigestTotal
open Aeneas Aeneas.Std Result NMX_R3_DigestWords NMX_R3_DigestPositive
attribute [local instance] Classical.propDecidable

noncomputable def outcome (b : Slice U8) (s : Nat) :
 core.result.Result (Array U32 8#usize) Unit :=
 if Canonical b s then .Ok (target b s) else .Err ()

/-- Total digest result, with a symbolic first-invalid-limb proof rather than
any fixed-input or all-success assumption. -/
theorem value (b : Slice U8) (s : Usize) (cap : b.val.length ≤ 768)
 (fit : s.val + 32 ≤ b.val.length) :
 NCV_Reference.digest b s = ok (outcome b s.val) := by
 by_cases all : Canonical b s.val
 · rw [outcome, if_pos all]
   exact NMX_R3_DigestPositive.value b s cap fit all
 · have existsBad : ∃ k, k < 8 ∧ ¬ (limb b s.val k).val < 2147483647 := by
    by_contra no
    apply all
    intro k hk
    by_contra invalid
    exact no ⟨k, hk, invalid⟩
   let bad := Nat.find existsBad
   have found := Nat.find_spec existsBad
   have bound : bad < 8 := found.1
   have invalid : ¬ (limb b s.val bad).val < 2147483647 := found.2
   have prior : ∀ j, j < bad → (limb b s.val j).val < 2147483647 := by
    intro j hj
    by_contra rejected
    have minimal : bad ≤ j := Nat.find_min' existsBad ⟨by omega, rejected⟩
    omega
   rw [outcome, if_neg all]
   apply NDB_DigestReject.rejected b s (limb b s.val) bad cap fit bound
   · intro i hi addr same
     exact read b s i.val (by omega) fit addr same
   · exact prior
   · exact invalid
#print axioms value
end NMX_R3_DigestTotal
