import NGK_COMBINED_IMPORT
set_option autoImplicit false
namespace AspisR1.NGQ_ScanLaws
open AspisV8R19.Q22WordScan

/-- Duplicate attempts consume draws while preserving the ordered survivors. -/
theorem duplicates (s : ScanState) (x n : Nat)
    (member : x ∈ s.accepted) (notFull : s.accepted.length ≠ 22)
    (budget : s.draws+n ≤ 64) :
    scan s (List.replicate n x)=({s with draws:=s.draws+n},false) := by
  induction n generalizing s with
  | zero => simp only [List.replicate_zero,scan,Nat.add_zero]
  | succ n ih =>
    have below : s.draws≠64 := by omega
    have nextBudget : s.draws+1+n≤64 := by omega
    simp only [List.replicate_succ,scan,notFull,below,or_self,if_false,keep,if_pos member]
    have h := ih {s with draws:=s.draws+1} member notFull nextBudget
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- A concrete stream shape can reject. This uses symbolic duplicate induction,
not kernel unfolding of all 64 recurrence cells. -/
theorem zero_stream_rejects :
    finish (scan ⟨[],0⟩ (List.replicate 64 0)).1=.error 1 := by
  have h := duplicates ⟨[0],1⟩ 0 63 (by simp only [List.mem_singleton])
    (by decide) (by decide)
  change finish (scan ⟨[],0⟩ (0 :: List.replicate 63 0)).1=.error 1
  simp only [scan,List.length_nil,show ¬(0=22 ∨ 0=64) by decide,if_false,
    keep,List.not_mem_nil,if_false,List.nil_append]
  rw [h]
  rfl

theorem keep_order (xs : List Nat) (x : Nat) :
    keep xs x=xs ∨ keep xs x=xs++[x] := by
  by_cases h : x∈xs
  · exact Or.inl (if_pos h)
  · exact Or.inr (if_neg h)

theorem keep_nodup (xs : List Nat) (x : Nat) (good : xs.Nodup) :
    (keep xs x).Nodup := by
  by_cases h : x∈xs
  · simpa only [keep,if_pos h] using good
  · simpa only [keep,if_neg h,List.concat_eq_append] using good.concat h

theorem scan_nodup (s : ScanState) (xs : List Nat) (good : s.accepted.Nodup) :
    (scan s xs).1.accepted.Nodup := by
  induction xs generalizing s with
  | nil => exact good
  | cons x xs ih =>
    simp only [scan]
    split
    · exact good
    · exact ih _ (keep_nodup _ _ good)

/-- The output list is the SAME survivor list in source order. -/
theorem success_positions (s : ScanState) (out : List Nat)
    (h : finish s=.ok out) : out=s.accepted ∧ out.length=22 := by
  unfold finish at h
  split at h
  · cases h; exact ⟨rfl,by assumption⟩
  · cases h

#print axioms duplicates
#print axioms zero_stream_rejects
#print axioms keep_order
#print axioms keep_nodup
#print axioms scan_nodup
#print axioms success_positions
end AspisR1.NGQ_ScanLaws
