import NMX_R3_FrontierCarrier
set_option autoImplicit false
namespace NMX_R3_FrontierCanonicalPositive
open Aeneas Aeneas.Std RSL NMX_R3_ByteCarrier NMX_R3_FrontierWords NMX_R3_FrontierCarrier
/-- Prefix invariant, proved symbolically before instantiation at depth20. -/
theorem accepted_prefix (t : Slice U8) (next : U64) :
 ∀ n, n ≤ 20 → (∀ k, k < n → At t next k) →
 TX2_217.frontierLoop (t.val.map byte) (long next) n = some (rows t n) := by
 intro n
 induction n with
 | zero => intro _ _; rfl
 | succ n ih =>
   intro bound good
   have prior := ih (by omega) (fun k hk => good k (by omega))
   rw [TX2_217.frontierLoop, prior]
   dsimp only
   rw [digest t n, if_pos (good n (by omega)).1]
   dsimp only
   rw [good_guard t next n (by omega) (good n (by omega))]
   simp only [Bool.false_eq_true, ↓reduceIte, rows, List.range_succ,
    List.map_append, List.map_cons, List.map_nil]
#print axioms accepted_prefix
end NMX_R3_FrontierCanonicalPositive
