import Mathlib.Data.List.Basic

/- The owned sequence semantics of the pinned slice::Iter<u8>::any body.
   The SDK iterator representation is checked separately by the symbolic
   next-step Kani certificate. This file does not assert SDK correspondence. -/
namespace S2CheckpointScanCompositionV1

abbrev Byte := Fin 256

/-- Result and unconsumed suffix, including the actual short circuit. -/
def scan : List Byte → Bool × List Byte
  | [] => (false, [])
  | b :: rest => if b.val = 0 then scan rest else (true, rest)

def join (left : Bool × List Byte) (right : List Byte) : Bool × List Byte :=
  if left.1 then (true, left.2 ++ right) else scan right

theorem false_suffix (bytes : List Byte) (h : (scan bytes).1 = false) :
    (scan bytes).2 = [] := by
  induction bytes with
  | nil => rfl
  | cons b rest ih =>
    by_cases hb : b.val = 0
    · simpa only [scan, if_pos hb] using ih (by simpa only [scan, if_pos hb] using h)
    · simp only [scan, if_neg hb, Prod.fst] at h
      contradiction

/-- Exact append law, preserving rejected/early-return suffixes. -/
theorem scan_append (left right : List Byte) :
    scan (left ++ right) = join (scan left) right := by
  induction left with
  | nil => simp [scan, join]
  | cons b rest ih =>
    by_cases hb : b.val = 0
    · simpa only [List.cons_append, scan, if_pos hb] using ih
    · simp only [List.cons_append, scan, if_neg hb, join, Prod.fst, Prod.snd, if_true]

def chunks : List (List Byte) → Bool × List Byte
  | [] => (false, [])
  | block :: rest =>
    let r := scan block
    if r.1 then (true, r.2 ++ rest.flatten) else chunks rest

/-- Induction over arbitrary chunk count; no 1768-byte normalization. -/
theorem chunks_eq_scan (blocks : List (List Byte)) :
    chunks blocks = scan blocks.flatten := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
    simp only [chunks, List.flatten_cons, scan_append, join]
    split
    · rfl
    · exact ih

theorem scan_false_iff (bytes : List Byte) :
    (scan bytes).1 = false ↔ ∀ b ∈ bytes, b.val = 0 := by
  induction bytes with
  | nil => simp [scan]
  | cons b rest ih =>
    by_cases hb : b.val = 0
    · have hb' : b = 0 := Fin.ext hb
      simpa [scan, hb, hb'] using ih
    · have hb' : b ≠ 0 := fun h => hb (congrArg Fin.val h)
      simp [scan, hb, hb']

/-- Total pointer-index range obligation for the SDK next-step contract. -/
theorem checkpoint_successor_range (cursor : Nat) (h : cursor < 1768) :
    cursor + 1 ≤ 1768 ∧ 1768 - (cursor + 1) + 1 = 1768 - cursor := by
  omega

theorem checkpoint_nonzero_iff (blocks : List (List Byte)) :
    (chunks blocks).1 = false ↔ ∀ b ∈ blocks.flatten, b.val = 0 := by
  rw [chunks_eq_scan, scan_false_iff]

#print axioms chunks_eq_scan
#print axioms checkpoint_nonzero_iff
#print axioms checkpoint_successor_range
end S2CheckpointScanCompositionV1
