import AspisV8R19.R522GammaWordPrefix

set_option autoImplicit false
namespace AspisV8R19.R523GammaGroupExecution
open Aeneas Aeneas.Std Result
open AspisV8.AffinePrimal AspisV8R19.R522GammaWordPrefix

/-- The checked multiply/add operation used for one bounded group-word term. -/
def checkedMac (s : U64) (ab : U64 × U64) : Result U64 := do
  let p ← (ab.1 * ab.2 : Result U64)
  (s + p : Result U64)

/-- A list of at most four bounded terms executes through the checked U64
multiply/add chain, with its natural accumulator and prefix bound. -/
theorem checkedMac_foldlM (n : Nat) (xs : List (U64 × U64)) (seed : U64)
    (hcount : n + xs.length ≤ 4) (hseed : seed.val ≤ n*m^2)
    (hops : ∀ ab ∈ xs, ab.1.val ≤ m ∧ ab.2.val ≤ m) :
    ∃ out, xs.foldlM checkedMac seed = .ok out ∧
      out.val = xs.foldl (fun s ab => s + ab.1.val * ab.2.val) seed.val ∧
      out.val ≤ (n + xs.length)*m^2 := by
  induction xs generalizing n seed with
  | nil =>
      refine ⟨seed, ?_, rfl, ?_⟩
      · rfl
      · simpa using hseed
  | cons ab xs ih =>
      have hab : ab.1.val ≤ m ∧ ab.2.val ≤ m := hops ab (by simp)
      have hn : n < 4 := by omega
      let next := U64.wrapping_add seed (U64.wrapping_mul ab.1 ab.2)
      have hstep : checkedMac seed ab = .ok next := by
        dsimp [checkedMac, next]
        exact checked_mac_prefix n seed ab.1 ab.2 hn hseed hab.1 hab.2
      have hnext := wrapping_mac_prefix n seed ab.1 ab.2 hn hseed hab.1 hab.2
      have hcount' : (n+1) + xs.length ≤ 4 := by
        simp at hcount
        omega
      have htail : ∀ bc ∈ xs, bc.1.val ≤ m ∧ bc.2.val ≤ m := by
        intro bc hbc
        exact hops bc (by simp [hbc])
      obtain ⟨out, hout, hval, hbound⟩ := ih (n := n+1) (seed := next) hcount' hnext.2 htail
      refine ⟨out, ?_, ?_, ?_⟩
      · simp only [List.foldlM_cons, hstep]
        exact hout
      · simpa [next, hnext.1] using hval
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbound

#print axioms checkedMac_foldlM
end AspisV8R19.R523GammaGroupExecution
