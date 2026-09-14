import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

/-!
# Order-preserving indexed weight folds

These are mathematical loop invariants for the proposed normalization of the
REAL `weight_at` source. They are not a Rust execution model. In particular,
canonical QM31 arithmetic, index bounds, and the generated helper's loop
simulation still have to be proved at the Aeneas layer.

No commutation is needed to remove iterators: multiplication order is retained.
-/
set_option autoImplicit false
namespace AspisK1.V7Tag73IndexedWeightFold
variable {K : Type*}

/-- A bounded, left-to-right multiply loop with an arbitrary starting index. -/
def mulScan [Mul K] (factor : Nat → K) : Nat → Nat → K → K
  | 0, _, acc => acc
  | n + 1, start, acc => mulScan factor n (start + 1) (acc * factor start)

/-- Specification with the same left-associated operation order. -/
def listMul [Mul K] (xs : List K) (acc : K) : K :=
  xs.foldl (fun a x => a * x) acc

theorem mulScan_eq_range_fold [Mul K]
    (factor : Nat → K) (n start : Nat) (acc : K) :
    mulScan factor n start acc =
      listMul ((List.range' start n).map factor) acc := by
  induction n generalizing start acc with
  | zero => rfl
  | succ n ih =>
      simpa only [mulScan, List.range'_succ, List.map_cons,
        listMul, List.foldl_cons] using ih (start + 1) (acc * factor start)

theorem mulScan_split [Mul K] (factor : Nat → K)
    (left right start : Nat) (acc : K) :
    mulScan factor (left + right) start acc =
      mulScan factor right (start + left) (mulScan factor left start acc) := by
  induction left generalizing start acc with
  | zero => simp [mulScan]
  | succ left ih =>
      simpa only [Nat.succ_add, mulScan, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using
        ih (start + 1) (acc * factor start)

theorem mulScan_factor_acc [Monoid K] (factor : Nat → K)
    (n start : Nat) (acc : K) :
    mulScan factor n start acc = acc * mulScan factor n start 1 := by
  induction n generalizing start acc with
  | zero => simp [mulScan]
  | succ n ih =>
      simp only [mulScan]
      rw [ih (start + 1) (acc * factor start), ih (start + 1) (1 * factor start)]
      simp only [one_mul, mul_assoc]

/-- Runtime big-endian bit order, stated without pretending Nat shifts are U32. -/
def bigEndianBit (index width coordinate : Nat) : Nat :=
  (index / 2 ^ (width - 1 - coordinate)) % 2

theorem bigEndianBit_lt_two (index width coordinate : Nat) :
    bigEndianBit index width coordinate < 2 :=
  Nat.mod_lt _ (by decide)

theorem bigEndianBit_last (index width : Nat) (positive : 0 < width) :
    bigEndianBit index width (width - 1) = index % 2 := by
  simp [bigEndianBit]

/-- Multilinear factors read ONE minus z only on the zero-bit branch. -/
def multilinearFactor [One K] [Sub K]
    (point : Nat → K) (index width coordinate : Nat) : K :=
  if bigEndianBit index width coordinate = 0
  then 1 - point coordinate else point coordinate

/-- Tensor skips are represented by multiplying by one. -/
def tensorFactor [One K]
    (point : Nat → K) (index width coordinate : Nat) : K :=
  if bigEndianBit index width coordinate = 0 then 1 else point coordinate

def tensorSkipScan [Monoid K] (point : Nat → K) (index width : Nat) :
    Nat → Nat → K → K
  | 0, _, acc => acc
  | n + 1, coordinate, acc =>
      tensorSkipScan point index width n (coordinate + 1)
        (if bigEndianBit index width coordinate = 0
         then acc else acc * point coordinate)

theorem tensorSkipScan_eq_mulScan [Monoid K]
    (point : Nat → K) (index width n coordinate : Nat) (acc : K) :
    tensorSkipScan point index width n coordinate acc =
      mulScan (tensorFactor point index width) n coordinate acc := by
  induction n generalizing coordinate acc with
  | zero => rfl
  | succ n ih =>
      simp only [tensorSkipScan, mulScan, tensorFactor]
      split_ifs with h
      · simpa only [mul_one] using ih (coordinate + 1) acc
      · exact ih (coordinate + 1) (acc * point coordinate)

/-- The zip loop stops at the shorter slice, INCLUDING malformed unequal slices. -/
theorem zipped_length {A B : Type*} (left : List A) (right : List B) :
    (left.zip right).length = min left.length right.length := by
  simp only [List.length_zip]

/-- A paired scan preserves the source's zip/truncation semantics. -/
def zipScan [Add K] (term : Nat → K) : Nat → Nat → K → K
  | 0, _, acc => acc
  | n + 1, index, acc => zipScan term n (index + 1) (acc + term index)

theorem zipScan_eq_range_fold [Add K]
    (term : Nat → K) (n start : Nat) (acc : K) :
    zipScan term n start acc =
      ((List.range' start n).map term).foldl (fun a x => a + x) acc := by
  induction n generalizing start acc with
  | zero => rfl
  | succ n ih =>
      simpa only [zipScan, List.range'_succ, List.map_cons,
        List.foldl_cons] using ih (start + 1) (acc + term start)

theorem simultaneous_bounds_iff_min (i left right : Nat) :
    (i < left ∧ i < right) ↔ i < min left right := by omega

theorem scan_index_within (start count width offset : Nat)
    (room : start + count ≤ width) (inside : offset < count) :
    start + offset < width := by omega

#print axioms mulScan_eq_range_fold
#print axioms mulScan_split
#print axioms tensorSkipScan_eq_mulScan
#print axioms zipScan_eq_range_fold
end AspisK1.V7Tag73IndexedWeightFold
