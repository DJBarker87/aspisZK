import FixedWidthDecoderWork
import R1SemanticPublicWire

/-! Public decoder primitives. A length visit, a bounded list lookup and a
fixed-width arithmetic/constructor operation are unit steps. The fixed tariff
includes all four (or eight) byte accesses and retained closure access. Inputs
to these primitives are capped by the calling cursor, including failures. -/
set_option autoImplicit false
namespace AspisR1.PublicPrimitiveDecoderWork
abbrev Byte := ExactLeafFieldCodec.Byte

def length : List Byte → Nat × Nat
  | [] => (0, 1)
  | _ :: xs => let r := length xs; (r.1 + 1, r.2 + 1)

theorem length_value (xs : List Byte) : (length xs).1 = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [length, List.length_cons, ih]

theorem length_work (xs : List Byte) : (length xs).2 = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [length, List.length_cons, ih]

/-- Primitive schedules: strict length scan, fixed-width byte accesses,
canonicality comparison and exact-field conversion. The generous constant
256 covers four accesses of at most four cells plus fixed word arithmetic;
1024 covers eight accesses of at most eight cells and index arithmetic.
It is independent of the value of the decoded word. -/
def field (xs : List Byte) : Option ExactLeafFieldCodec.M31Exact × Nat :=
  (ExactLeafFieldCodec.decodeM31 xs, (length xs).2 + 256)

def index (xs : List Byte) : Option PublicIndexCodec.Index × Nat :=
  (PublicIndexListCodec.decode xs, (length xs).2 + 1024)

theorem field_value (xs : List Byte) : (field xs).1 = ExactLeafFieldCodec.decodeM31 xs := rfl

theorem field_work (xs : List Byte) (h : xs.length ≤ 4) : (field xs).2 ≤ 261 := by
  simp only [field, length_work]; omega

theorem index_value (xs : List Byte) : (index xs).1 = PublicIndexListCodec.decode xs := rfl

theorem index_work (xs : List Byte) (h : xs.length ≤ 8) : (index xs).2 ≤ 1033 := by
  simp only [index, length_work]; omega

def digest (xs : List Byte) := FixedWidthDecoderWork.decode field 4 8 xs

theorem digest_value (xs : List Byte) : (digest xs).1 = PublicFieldBlockCodec.decodeDigest xs :=
  FixedWidthDecoderWork.value field 4 8 xs

theorem digest_work (xs : List Byte) : (digest xs).2 ≤ 2225 :=
  FixedWidthDecoderWork.work field 4 8 261 field_work xs

def frontier (xs : List Byte) := FixedWidthDecoderWork.decode digest 32 20 xs

theorem frontier_value (xs : List Byte) :
    (frontier xs).1 = PublicFieldBlockCodec.decodeFrontier xs := by
  rw [frontier, FixedWidthDecoderWork.value]
  simp only [digest_value, PublicFieldBlockCodec.decodeFrontier]

theorem frontier_work (xs : List Byte) : (frontier xs).2 ≤ 46521 :=
  FixedWidthDecoderWork.work digest 32 20 2225 (fun bs _ => digest_work bs) xs

/-- Capped cursor. Both prefix copying and suffix traversal are charged even
when decoding fails. This is conservative and gives a uniform failure bound. -/
def read {A : Type} (n : Nat) (d : List Byte → Option A × Nat)
    (xs : List Byte) : Option (A × List Byte) × Nat :=
  let p := BinLeafListWork.take n xs
  let s := BinLeafListWork.drop n xs
  let r := d p.1
  (r.1.map (fun a => (a, s.1)), p.2 + s.2 + r.2 + 2)

theorem read_value {A : Type} (n : Nat) (d : List Byte → Option A × Nat)
    (xs : List Byte) : (read n d xs).1 =
      PublicByteCursor.read n (fun bs => (d bs).1) xs := by
  simp only [read, PublicByteCursor.read, BinLeafListWork.take_value,
    BinLeafListWork.drop_value]

theorem read_work {A : Type} (n c : Nat) (d : List Byte → Option A × Nat)
    (hd : ∀ bs, bs.length ≤ n → (d bs).2 ≤ c) (xs : List Byte) :
    (read n d xs).2 ≤ 3*n+c+4 := by
  have hp := BinLeafListWork.take_work n xs
  have hs := BinLeafListWork.drop_work n xs
  have hh := hd (BinLeafListWork.take n xs).1 (by
    rw [BinLeafListWork.take_value]; exact List.length_take_le _ _)
  change _ + _ + _ + 2 ≤ _
  omega

#print axioms length_value
#print axioms length_work
#print axioms field_value
#print axioms field_work
#print axioms index_value
#print axioms index_work
#print axioms digest_value
#print axioms digest_work
#print axioms frontier_value
#print axioms frontier_work
#print axioms read_value
#print axioms read_work
end AspisR1.PublicPrimitiveDecoderWork
