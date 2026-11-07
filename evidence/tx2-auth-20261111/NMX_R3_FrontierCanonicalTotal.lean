import NMX_R3_FrontierCanonicalFailure
import NMX_R3_FrontierInvariant
set_option autoImplicit false
namespace NMX_R3_FrontierCanonicalTotal
open Aeneas Aeneas.Std RSL NMX_R3_ByteCarrier NMX_R3_FrontierWords NMX_R3_FrontierCarrier
attribute [local instance] Classical.propDecidable
/-- The canonical loop's complete outcome, including every first-failure index. -/
theorem value (t : Slice U8) (next : U64) :
 TX2_217.frontierLoop (t.val.map byte) (long next) 20 =
 if Valid t next then some (rows t 20) else none := by
 by_cases valid : Valid t next
 · rw [if_pos valid]
   exact NMX_R3_FrontierCanonicalPositive.accepted_prefix t next 20 (by omega) valid
 · rw [if_neg valid]
   have existsBad : ∃ k, k < 20 ∧ ¬ At t next k := by
    by_contra no
    apply valid
    intro k hk
    by_contra rejected
    exact no ⟨k,hk,rejected⟩
   let bad := Nat.find existsBad
   have found := Nat.find_spec existsBad
   have prior : ∀ k, k < bad → At t next k := by
    intro k hk
    by_contra no
    have minimal : bad ≤ k := Nat.find_min' existsBad ⟨by omega,no⟩
    omega
   have first := NMX_R3_FrontierCanonicalFailure.first t next bad found.1 prior found.2
   have suffix := NMX_R3_FrontierInvariant.rejection_suffix (t.val.map byte)
    (long next) (bad+1) (20-(bad+1)) first
   have extent : bad+1+(20-(bad+1)) = 20 := by have := found.1; omega
   rwa [extent] at suffix
#print axioms value
end NMX_R3_FrontierCanonicalTotal
