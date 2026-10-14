import R1QueryDecoder

/-! Structural facts about the finite missing-squeeze answer list. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QueryDecoder

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem missing_nodup (p : Params M Cv L) (T : Table (Addr L) State) (endpoint : State) :
    (missing p T endpoint).Nodup := by
  unfold missing
  cases h : DuplexSeek.seek p T 9 endpoint <;> simp [h, List.nodup_dedup]

theorem missing_mem_of_seek (p : Params M Cv L) (T : Table (Addr L) State)
    (endpoint : State) (a : Addr L) (xs : List State)
    (hseek : DuplexSeek.seek p T 9 endpoint = some (a, xs)) (b : Addr L)
    (hb : b ∈ missing p T endpoint) :
    ∃ z ∈ xs.dropLast, b = squeezeA p z ∧ T b = none := by
  unfold missing at hb
  rw [hseek] at hb
  rw [List.mem_dedup, List.mem_filter, List.mem_map] at hb
  obtain ⟨⟨z, hz, hzb⟩, hnone⟩ := hb
  refine ⟨z, hz, ?_, ?_⟩
  · exact hzb.symm
  · exact Option.isNone_iff_eq_none.mp hnone

theorem missing_mem_states (p : Params M Cv L) (T : Table (Addr L) State)
    (endpoint : State) (a : Addr L) (s : Nat → State) (n : Nat)
    (hseek : DuplexSeek.seek p T 9 endpoint = some (a, QueryStateList.states s n))
    (b : Addr L) (hb : b ∈ missing p T endpoint) :
    ∃ j < n, b = squeezeA p (s j) ∧ T b = none := by
  obtain ⟨z, hz, hzb, hT⟩ := missing_mem_of_seek p T endpoint a
    (QueryStateList.states s n) hseek b hb
  rw [QueryStateList.states_dropLast] at hz
  obtain ⟨j, hj, hjs⟩ := List.mem_map.mp hz
  refine ⟨j, List.mem_range.mp hj, ?_, hT⟩
  rw [← hjs] at hzb
  exact hzb

theorem parseAbsorb_squeeze_none (p : Params M Cv L) (s : State) :
    parseAbsorb (squeezeA p s) = none := by
  have hlen : (squeezeA p s).toBytes.length = 33 := by
    simp [squeezeA, Addr.toBytes_ofBytes, squeeze, bytes_length]
  simp only [parseAbsorb, hlen]
  simp

#print axioms missing_nodup
#print axioms missing_mem_of_seek
#print axioms missing_mem_states
#print axioms parseAbsorb_squeeze_none

end AspisR1.QueryDecoder
end
