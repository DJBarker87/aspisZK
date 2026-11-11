import OraclePortSelectedDraft

/-! The Aspis one-transaction verifier: the summed proof format as a stored-byte
layout over R1's `Parsed` carrier (item M1 of ONE-TRANSACTION-GAME.md).

Kind of result: MODEL DEFINITIONS AND LEMMAS in R1's stored-proof model. The
summed format keeps R1's layout up to `OFF_NODES` = 28359 (header 16 bytes,
semantic rows, y1, inactive, round polynomials, folded root, final message, 22
openings of 832 bytes at 10055), then three merged node slots of 296, 296 and
254 nodes (`summed_format::SLOT_NODES`, fused.rs:724) and the 384-byte
certificate (55431..55815). Only the header (magic `ASPIS\0\0\x02`, length
55815) differs from R1's `OraclePortHeader.accepts` before `OFF_NODES`.

NOT established here: that `parse_shape_summed` and `canonical_scan` in the
Rust compute `acceptsSummed` and R1's `scan` (source refinement). -/
set_option autoImplicit false
noncomputable section
namespace AspisOneTx
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1 AspisR1.OraclePortCompactDraft AspisR1.OraclePortSelectedDraft

/-- `ASPIS`, two zero bytes, format number 2 (fused.rs:721). -/
def summedMagic : Bytes := [65,83,80,73,83,0,0,2]

/-- R1's four header tests with the summed length and magic (parse_shape_summed). -/
def acceptsSummed (proof : Bytes) : Bool := decide (
  proof.length = 55815 ∧ proof.take 8 = summedMagic ∧
  proof[8]? = some 2 ∧ (proof.drop 9).take 7 = List.replicate 7 0)

theorem acceptsSummed_iff (proof : Bytes) : acceptsSummed proof = true ↔
    proof.length = 55815 ∧ proof.take 8 = summedMagic ∧
    proof[8]? = some 2 ∧ (proof.drop 9).take 7 = List.replicate 7 0 := by
  simp only [acceptsSummed, decide_eq_true_eq]

attribute [local instance] Classical.propDecidable

/-- R1's `parse` with the summed header; scan and semantic rows unchanged
(they read only bytes below 28359, which the two formats share). -/
def parseSummed (b : Bytes) : Option Parsed := do
  if acceptsSummed b = false then none else do
    if ¬ scan b then none else do
      let rs ← semanticRows 27 0 (slice b 48 6983)
      pure ⟨b,rs⟩

/-- Worst-case supplied nodes of the three merged multiproofs (C1, C2, folded). -/
def mergedCapacity (kind : Nat) : Nat := [296,296,254][kind]?.getD 0

/-- Start of a merged slot: R1's `OFF_NODES` plus the earlier slots. -/
def mergedStart (kind : Nat) : Nat := 28359 + 32 * ((List.range kind).map mergedCapacity).sum

def certificateStart : Nat := mergedStart 3

theorem nodes_offset : 10055 + 22*832 = 28359 := rfl
theorem mergedStart_values :
    mergedStart 0 = 28359 ∧ mergedStart 1 = 37831 ∧ mergedStart 2 = 47303 := ⟨rfl, rfl, rfl⟩
theorem certificateStart_eq : certificateStart = 55431 := rfl
theorem summed_total : certificateStart + 384 = 55815 := rfl

theorem parseSummed_header (b : Bytes) (p : Parsed) (h : parseSummed b = some p) :
    acceptsSummed b = true ∧ p.wire = b := by
  unfold parseSummed at h
  split at h
  · contradiction
  · rename_i hh
    have hb : acceptsSummed b = true := Bool.eq_true_of_not_eq_false hh
    split at h
    · contradiction
    · cases hs : semanticRows 27 0 (slice b 48 6983) <;> simp [hs] at h
      subst p
      exact ⟨hb,rfl⟩

theorem parsedSummed_length (b : Bytes) (p : Parsed) (h : parseSummed b = some p) :
    p.wire.length = 55815 := by
  rw [(parseSummed_header b p h).2]
  exact ((acceptsSummed_iff b).mp (parseSummed_header b p h).1).1

theorem slice_length (b : Bytes) (offset size : Nat) (bound : offset+size ≤ b.length) :
    (slice b offset size).length = size := by
  simp only [slice,List.length_take,List.length_drop]
  exact Nat.min_eq_left (by omega)

/-- Copy of `OraclePortStoredWidthsC4.opening_fields` for the summed parser. -/
theorem opening_fields_summed (b : Bytes) (p : Parsed) (parsed : parseSummed b = some p)
    (pos : Nat) (bound : pos < 22) :
    ((opening p pos).take 480).length = 480 ∧
    (slice (opening p pos) 480 128).length = 128 ∧
    (slice (opening p pos) 608 32).length = 32 ∧
    (slice (opening p pos) 640 32).length = 32 ∧
    (slice (opening p pos) 672 128).length = 128 ∧
    (slice (opening p pos) 800 32).length = 32 := by
  have width : (opening p pos).length = 832 := by
    apply slice_length
    rw [parsedSummed_length b p parsed]
    omega
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simp only [List.length_take,width]
    rfl
  all_goals
    apply slice_length
    omega

/-- Every merged slot lies inside the parsed proof, before the certificate. -/
theorem merged_slot_within (b : Bytes) (p : Parsed) (parsed : parseSummed b = some p)
    (kind : Nat) (hk : kind < 3) :
    mergedStart kind + 32 * mergedCapacity kind ≤ certificateStart ∧
      certificateStart ≤ p.wire.length := by
  rw [parsedSummed_length b p parsed]
  interval_cases kind <;> exact ⟨by decide, by decide⟩

#print axioms acceptsSummed_iff
#print axioms certificateStart_eq
#print axioms parseSummed_header
#print axioms parsedSummed_length
#print axioms opening_fields_summed
#print axioms merged_slot_within
end AspisOneTx
end
