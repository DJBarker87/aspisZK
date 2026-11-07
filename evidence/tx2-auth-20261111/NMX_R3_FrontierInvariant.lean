import RSL_TX2_217
set_option autoImplicit false
namespace NMX_R3_FrontierInvariant
open RSL
/-- The canonical loop's returned frontier has exactly one node for every
completed iteration; a rejected prefix cannot acquire a successful suffix. -/
theorem length (t : Bytes) (next : UInt64) (n : Nat) (out : List Digest)
    (returned : TX2_217.frontierLoop t next n = some out) : out.length = n := by
  induction n generalizing out with
  | zero =>
    simp only [TX2_217.frontierLoop, Option.some.injEq] at returned
    rw [← returned]
    rfl
  | succ n ih =>
    simp only [TX2_217.frontierLoop] at returned
    cases prior : TX2_217.frontierLoop t next n with
    | none => simp only [prior] at returned; contradiction
    | some acc =>
      simp only [prior] at returned
      split at returned
      · contradiction
      · split at returned
        · contradiction
        · cases returned
          simp only [List.length_append, List.length_singleton]
          exact congrArg (· + 1) (ih acc prior)

/-- An aborting/rejecting prefix remains rejected for every later extent. -/
theorem rejection_suffix (t : Bytes) (next : UInt64) (n k : Nat)
    (rejected : TX2_217.frontierLoop t next n = none) :
    TX2_217.frontierLoop t next (n+k) = none := by
  induction k with
  | zero => exact rejected
  | succ k ih =>
    rw [Nat.add_succ]
    rw [TX2_217.frontierLoop]
    rw [ih]
#print axioms length
#print axioms rejection_suffix
end NMX_R3_FrontierInvariant
