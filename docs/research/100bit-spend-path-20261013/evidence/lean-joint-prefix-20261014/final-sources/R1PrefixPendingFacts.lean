import R1PrefixAnswers
import R1QueryMissingFacts
import R1TableStateSeparation

/-! Structural facts about answer cells required by a semantic prefix. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.PrefixPendingFacts

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem missing_mem (p : Params M Cv L) (T : Table (Addr L) State)
    (rs : List (Rec M)) (b : Addr L)
    (hb : b ∈ PrefixAnswers.missing p T rs) :
    ∃ r ∈ rs, b = squeezeA p r.2.1 ∧ T b = none := by
  unfold PrefixAnswers.missing at hb
  rw [List.mem_dedup, List.mem_filter, List.mem_map] at hb
  obtain ⟨⟨r, hr, hbr⟩, hnone⟩ := hb
  exact ⟨r, hr, hbr.symm, of_decide_eq_true hnone⟩

theorem pending_facts (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (c : Addr L) (hc : Read tr c) (hparsec : (parseAbsorb c).isSome)
    (rs : List (Rec M))
    (hknown : ∀ r ∈ rs, ∃ a, tableBefore emptyTable tr c a = some r.2.1)
    (hreads : ∀ r ∈ rs, Read tr (squeezeA p r.2.1)) :
    ∀ b ∈ PrefixAnswers.missing p (tableBefore emptyTable tr c) rs,
      tableBefore emptyTable tr c b = none ∧ Read tr b ∧
        b ≠ c ∧ b ≠ squeezeA p (H c) ∧ b ≠ advanceA p (H c) := by
  intro b hb
  obtain ⟨r, hr, rfl, hnone⟩ := missing_mem p (tableBefore emptyTable tr c) rs b hb
  refine ⟨hnone, hreads r hr, ?_, ?_, ?_⟩
  · intro heq
    have hparse : parseAbsorb (squeezeA p r.2.1) = none :=
      QueryDecoder.parseAbsorb_squeeze_none p r.2.1
    rw [heq] at hparse
    rw [hparse] at hparsec
    contradiction
  · rcases hknown r hr with ⟨a, hcell⟩
    have hne := TableStateSeparation.known_ne_endpoint p H tr Qtot
      hcons hQ hold c hc a r.2.1 hcell
    intro heq
    have hsqueeze : squeezeA p r.2.1 = squeezeA p (H c) := heq
    exact hne (squeezeA_injective p hsqueeze)
  · intro heq
    exact squeezeA_ne_advanceA' p r.2.1 (H c) heq

#print axioms missing_mem
#print axioms pending_facts

end AspisR1.PrefixPendingFacts
end
