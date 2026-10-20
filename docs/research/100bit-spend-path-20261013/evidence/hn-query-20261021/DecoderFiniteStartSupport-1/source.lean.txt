import DecoderQueryAccounting

set_option autoImplicit false
noncomputable section
namespace AspisR1.DecoderFiniteStartSupport
open FS FS2 R0C.V3 AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open DecodedFirstReadUnionBound
attribute [local instance] Classical.propDecidable
variable {X M C I A Y : Type} [DecidableEq I]

/-- Symbolic charging to distinct allowed addresses, removing each cached
address from the finite residual support. No concrete log is evaluated. -/
theorem starts_le_support (decoder : Dec X M C I A Y)
    (t : Table I A) (tr : List (I × A)) (s : Finset I)
    (hs : ∀ q ∈ tr, ∀ U : Table I A, decoder q.1 U ≠ none → q.1 ∈ s) :
    decoderFirstReads decoder t tr ≤ (s.filter (fun k => t k = none)).card := by
  induction tr generalizing t with
  | nil => exact Nat.zero_le _
  | cons q tr ih =>
    have ht := ih (put t q.1 q.2) (fun r hr => hs r (List.mem_cons_of_mem q hr))
    have he : s.filter (fun k => put t q.1 q.2 k = none) =
        (s.filter (fun k => t k = none)).erase q.1 := by
      ext k
      by_cases hk : k = q.1
      · subst k; simp [put]
      · simp [put, hk, Finset.mem_filter, Finset.mem_erase, and_comm, and_left_comm]
    rw [he] at ht
    rw [decoderFirstReads]
    split
    · rename_i hq
      have hm : q.1 ∈ s.filter (fun k => t k = none) :=
        Finset.mem_filter.mpr ⟨hs q (List.mem_cons_self ..) t hq.2, hq.1⟩
      have hc := Finset.card_erase_add_one hm
      omega
    · simp only [zero_add]
      exact ht.trans (Finset.card_le_card (Finset.erase_subset _ _))

#print axioms starts_le_support
end AspisR1.DecoderFiniteStartSupport
end
