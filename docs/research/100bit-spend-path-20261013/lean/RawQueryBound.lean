import R1RawOpening
import R1BoundedQueries

/-! Compose the bounded query law with the explicit seven coefficient rows.
The rows remain supplied data: this theorem does not identify them with Rust
constructors or with the semantic spend relation. -/

set_option autoImplicit false
noncomputable section
namespace AspisR1.RawQueryBound

open AspisCircleGroupOrder AspisR1.MatchingSupport AspisR1.RawOpening
open AspisV8R19.SourceDuplexStep AspisV8R19.CausalFirstHitUnionBound
open R0C.V3.Q22

variable {K E : Type} [Field K] [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) E]

theorem raw_no_claims_bounded_q22 (iota : K →+* E)
    (raw : Fin 7 → Fin 1024 → K) (d : Data E) (s : State)
    (hgood : Good (withRows iota raw d))
    (haccepted : rawAcceptedPairing iota raw d)
    (hnot : ¬ rawClaims iota raw d) :
    chainE (fun bs xs => indicator
      ((chalSet (scanOut 8 q0 bs xs s).1).card = 22 ∧
        chalSet (scanOut 8 q0 bs xs s).1 ⊆ matchingSet (withRows iota raw d))) 8 ≤
      (Nat.choose 9557 22 : ℚ) / (Nat.choose 262144 22 : ℚ) := by
  apply AspisR1.BoundedQueries.no_claims_bounded_q22
    (withRows iota raw d) s hgood
    ((accepted_pairing_iff_raw iota raw d).mpr haccepted)
  intro hclaims
  exact hnot ((claims_iff_raw iota raw d).mp hclaims)

#print axioms raw_no_claims_bounded_q22
end AspisR1.RawQueryBound
end
