import NMX_R3_FrontierCanonicalPositive
set_option autoImplicit false
namespace NMX_R3_FrontierCanonicalFailure
open Aeneas Aeneas.Std RSL NMX_R3_ByteCarrier NMX_R3_FrontierWords NMX_R3_FrontierCarrier

theorem first (t : Slice U8) (next : U64) (bad : Nat) (bound : bad < 20)
 (prior : ∀ k, k < bad → At t next k) (rejected : ¬ At t next bad) :
 TX2_217.frontierLoop (t.val.map byte) (long next) (bad+1) = none := by
 classical
 rw [TX2_217.frontierLoop,
  NMX_R3_FrontierCanonicalPositive.accepted_prefix t next bad (by omega) prior]
 dsimp only
 rw [digest t bad]
 by_cases canonical : NMX_R3_DigestPositive.Canonical t (48+32*bad)
 · rw [if_pos canonical]
   dsimp only
   rw [bad_guard t next bad bound canonical rejected]
   rfl
 · rw [if_neg canonical]
#print axioms first
end NMX_R3_FrontierCanonicalFailure
