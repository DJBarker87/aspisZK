import KMZ_TypedInside
import KMZ_TypedExterior
import KMZ_IteratorEmpty
import KMZ_IteratorLast
import KMZ_IteratorInterior
import KMZ_IteratorSuffix
set_option autoImplicit false
namespace KMZ_LPm_K001
open KMX_CopyMeaning
/-- Typed value/frame and one iterator transition. Actual Vec/iterator executions
are the separately controlled Rust split obligations. -/
theorem result {α : Type} (raw before : Nat → α) (i : Nat) (hi : i≤64) :
 (∀ k, k<64 → loop raw before 0 64 k=raw k) ∧
 (64-i=0 ↔ i=64) ∧
 (i<64 → loop raw before 0 64 i=raw i ∧ 64-(i+1)=63-i) ∧
 (∀ j, j<64-(i+1) → loop raw before 0 64 (i+1+j)=raw (i+1+j)) ∧
 (∀ k, k=0 ∨ 65≤k → loop (fun t => raw (t-1)) before 1 64 k=before k) := by
 refine ⟨?_, ?_, ?_, ?_, ?_⟩
 · intro k hk
   exact KMZ_TypedInside.result raw before k hk
 · omega
 · intro h
   exact ⟨KMZ_TypedInside.result raw before i h, by omega⟩
 · intro j hj
   exact KMZ_TypedInside.result raw before (i+1+j) (by omega)
 · intro k hk
   exact KMZ_TypedExterior.result (fun t => raw (t-1)) before k hk
#print axioms result
end KMZ_LPm_K001
