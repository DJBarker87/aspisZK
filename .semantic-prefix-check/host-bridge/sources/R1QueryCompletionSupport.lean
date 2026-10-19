import R1QueryDecoder

/-! Congruence facts for query completion and recovery. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QueryCompletion

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem complete_congr (p : Params M Cv L) (T : Table (Addr L) State)
    (acc1 acc2 : Addr L → State) (xs : List State)
    (h : ∀ s ∈ xs.dropLast, T (squeezeA p s) = none →
      acc1 (squeezeA p s) = acc2 (squeezeA p s)) :
    complete p T acc1 xs = complete p T acc2 xs := by
  unfold complete
  congr 1
  apply List.map_congr_left
  intro s hs
  unfold readCell
  cases hT : T (squeezeA p s) with
  | none => simp [hT, h s hs hT]
  | some v => simp [hT]

end AspisR1.QueryCompletion

namespace AspisR1.QueryDecoder

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem recover_congr_on_missing (p : Params M Cv L)
    (T : Table (Addr L) State) (acc1 acc2 : Addr L → State)
    (endpoint : State)
    (h : ∀ b, b ∈ missing p T endpoint → acc1 b = acc2 b) :
    recover p T acc1 endpoint = recover p T acc2 endpoint := by
  unfold recover
  cases hs : DuplexSeek.seek p T 9 endpoint with
  | none => rfl
  | some r =>
      simp only [Option.map_some]
      apply congrArg some
      apply congrArg (fun z => (r.1, z))
      apply AspisR1.QueryCompletion.complete_congr
      intro s hsDrop hnone
      have hmem : squeezeA p s ∈ missing p T endpoint := by
        unfold missing
        rw [hs]
        apply List.mem_dedup.mpr
        apply List.mem_filter.mpr
        constructor
        · apply List.mem_map.mpr
          exact ⟨s, hsDrop, rfl⟩
        · simpa only [Option.isNone_iff_eq_none] using hnone
      exact h (squeezeA p s) hmem

theorem recover_update (p : Params M Cv L) (T : Table (Addr L) State)
    (acc : Addr L → State) (endpoint : State) (c : Addr L) (v : State)
    (hc : c ∉ missing p T endpoint) :
    recover p T (Function.update acc c v) endpoint = recover p T acc endpoint := by
  apply recover_congr_on_missing
  intro b hb
  have hbc : b ≠ c := by
    intro heq
    subst b
    exact hc hb
  simp [Function.update_of_ne hbc]

#print axioms AspisR1.QueryCompletion.complete_congr
#print axioms recover_congr_on_missing
#print axioms recover_update

end AspisR1.QueryDecoder
end
