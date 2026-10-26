import PublicPrimitiveDecoderWork
import BinEagerWordsReads

/-! Typed cache consumption. Lookup traversals include misses. Strict typed
leaf decoding uses capped cursors; no unbounded stored-byte-length premise is
needed for the outer C1/C2/folded decoders. Later Fin.cons projections have
at most 26+4+4 closure tests, included in the per-demand tariff. -/
set_option autoImplicit false
namespace AspisR1.BinTypedCacheWork
open PublicPrimitiveDecoderWork
abbrev Leaf := BinEagerWordsReads.Leaf

def lookup {A : Type} : List A → Nat → Option A × Nat
  | [], _ => (none, 1)
  | a :: _, 0 => (some a, 1)
  | _ :: xs, i+1 => let r := lookup xs i; (r.1, r.2+1)

theorem lookup_value {A : Type} (xs : List A) (i : Nat) :
    (lookup xs i).1 = xs[i]? := by
  induction xs generalizing i with
  | nil => simp only [lookup, List.getElem?_nil]
  | cons a xs ih => cases i <;> simp only [lookup, List.getElem?_cons_zero,
      List.getElem?_cons_succ, ih]

theorem lookup_work {A : Type} (xs : List A) (i : Nat) :
    (lookup xs i).2 ≤ i+1 := by
  induction xs generalizing i with
  | nil => simp only [lookup]; omega
  | cons a xs ih =>
    cases i with
    | zero => exact Nat.le_refl _
    | succ i => have ht := ih i; change (lookup xs i).2+1 ≤ _; omega

def cached {n : Nat} (xs : List Leaf) (i : Fin n) : Leaf × Nat :=
  let r := lookup xs i.val
  (r.1.getD none, r.2+2)

theorem cached_value {n : Nat} (xs : List Leaf) (i : Fin n) :
    (cached xs i).1 = BinEagerWordsReads.cached xs i := by
  simp only [cached, lookup_value, BinEagerWordsReads.cached]

theorem cached_work {n : Nat} (xs : List Leaf) (i : Fin n) :
    (cached xs i).2 ≤ n+2 := by
  have hi := i.isLt
  have hw := lookup_work xs i.val
  change (lookup xs i.val).2+2 ≤ n+2
  omega

def qm31 (xs : List Byte) : Option ExactLeafFieldCodec.QM31Exact × Nat :=
  (ExactLeafFieldCodec.decodeQM31 xs, (length xs).2+4096)
def wide (xs : List Byte) : Option FoldedLeafCodec.Wide × Nat :=
  (FoldedLeafCodec.decodeWide xs, (length xs).2+16384)

theorem qm31_work (xs : List Byte) (h : xs.length ≤ 16) : (qm31 xs).2 ≤ 4113 := by
  simp only [qm31, length_work]; omega
theorem wide_work (xs : List Byte) (h : xs.length ≤ 32) : (wide xs).2 ≤ 16417 := by
  simp only [wide, length_work]; omega

def c1slot (xs : List Byte) : Option MixedLeafEncoding.C1Slot × Nat :=
  let p := BinLeafListWork.take 104 xs
  let s := BinLeafListWork.drop 104 xs
  let w := FixedWidthDecoderWork.decode field 4 26 p.1
  let t := qm31 s.1
  (w.1.bind (fun words => t.1.map (fun tail => (words, tail))),
    p.2+s.2+w.2+t.2+5)

theorem c1slot_value (xs : List Byte) : (c1slot xs).1 = MixedLeafDecoder.decodeC1Slot xs := by
  simp only [c1slot, BinLeafListWork.take_value, BinLeafListWork.drop_value,
    FixedWidthDecoderWork.value, field_value, qm31, MixedLeafDecoder.decodeC1Slot]
  cases FixedWidthDecoder.decode ExactLeafFieldCodec.decodeM31 4 26 (xs.take 104) <;>
    cases ExactLeafFieldCodec.decodeQM31 (xs.drop 104) <;> rfl

theorem c1slot_work (xs : List Byte) (h : xs.length ≤ 120) : (c1slot xs).2 ≤ 12000 := by
  have hp := BinLeafListWork.take_work 104 xs
  have hs := BinLeafListWork.drop_work 104 xs
  have hw := FixedWidthDecoderWork.work field 4 26 261 field_work
    (BinLeafListWork.take 104 xs).1
  have ht := qm31_work (BinLeafListWork.drop 104 xs).1 (by
    rw [BinLeafListWork.drop_value, List.length_drop]; omega)
  change _+_+_+_+5 ≤ _
  omega

def c2slot (xs : List Byte) := FixedWidthDecoderWork.decode qm31 16 2 xs

theorem c2slot_value (xs : List Byte) : (c2slot xs).1 = MixedLeafDecoder.decodeC2Slot xs :=
  FixedWidthDecoderWork.value qm31 16 2 xs

theorem c2slot_work (xs : List Byte) : (c2slot xs).2 ≤ 8333 :=
  FixedWidthDecoderWork.work qm31 16 2 4113 qm31_work xs

def c1 (xs : List Byte) := FixedWidthDecoderWork.decode c1slot 120 4 xs
 def c2 (xs : List Byte) := FixedWidthDecoderWork.decode c2slot 32 4 xs
 def folded (xs : List Byte) := FixedWidthDecoderWork.decode wide 32 4 xs

theorem c1_value (xs : List Byte) : (c1 xs).1 = MixedLeafDecoder.decodeC1 xs := by
  simp only [c1, FixedWidthDecoderWork.value, c1slot_value, MixedLeafDecoder.decodeC1]
theorem c2_value (xs : List Byte) : (c2 xs).1 = MixedLeafDecoder.decodeC2 xs := by
  simp only [c2, FixedWidthDecoderWork.value, c2slot_value, MixedLeafDecoder.decodeC2]
theorem folded_value (xs : List Byte) : (folded xs).1 = FoldedLeafCodec.decodeFolded xs :=
  FixedWidthDecoderWork.value wide 32 4 xs

theorem c1_work (xs : List Byte) : (c1 xs).2 ≤ 49461 :=
  FixedWidthDecoderWork.work c1slot 120 4 12000 c1slot_work xs
theorem c2_work (xs : List Byte) : (c2 xs).2 ≤ 33737 :=
  FixedWidthDecoderWork.work c2slot 32 4 8333 (fun bs _ => c2slot_work bs) xs
theorem folded_work (xs : List Byte) : (folded xs).2 ≤ 66073 :=
  FixedWidthDecoderWork.work wide 32 4 16417 wide_work xs

/-- One cache demand, including decode, failed optional lookup and a fixed
projection tariff. This returns the typed leaf; selecting its fixed slot and
lane incurs at most 64 additional constructor/closure operations. -/
def demand {A : Type} {n : Nat} (d : List Byte → Option A × Nat)
    (xs : List Leaf) (i : Fin n) : Option A × Nat :=
  let r := cached xs i
  match r.1 with
  | none => (none, r.2+64)
  | some bs => let t := d bs; (t.1, r.2+t.2+64)

theorem demand_value {A : Type} {n : Nat} (d : List Byte → Option A × Nat)
    (xs : List Leaf) (i : Fin n) : (demand d xs i).1 =
      (BinEagerWordsReads.cached xs i).bind (fun bs => (d bs).1) := by
  simp only [demand, cached_value]
  cases BinEagerWordsReads.cached xs i <;> rfl

theorem demand_work {A : Type} {n : Nat} (d : List Byte → Option A × Nat)
    (c : Nat) (hd : ∀ bs, (d bs).2 ≤ c) (xs : List Leaf) (i : Fin n) :
    (demand d xs i).2 ≤ n+c+66 := by
  have hr := cached_work xs i
  unfold demand
  dsimp only
  split
  · dsimp only; omega
  · rename_i bs h
    have ht := hd bs
    dsimp only; omega

#print axioms lookup_value
#print axioms lookup_work
#print axioms cached_value
#print axioms cached_work
#print axioms qm31_work
#print axioms wide_work
#print axioms c1slot_value
#print axioms c1slot_work
#print axioms c2slot_value
#print axioms c2slot_work
#print axioms c1_value
#print axioms c2_value
#print axioms folded_value
#print axioms c1_work
#print axioms c2_work
#print axioms folded_work
#print axioms demand_value
#print axioms demand_work
end AspisR1.BinTypedCacheWork
