import BinLeafLengthWork

/-! A value-equivalent replacement for the leaf parser's two full length
traversals. Charges only these tests; drop/take, equality and bytes remain
separate accounting obligations. This is not full extractor instrumentation. -/
set_option autoImplicit false
namespace AspisR1.BinLeafBoundedLength
open BinMerkle32Path
open BinMerkleLeafRecovery (LeafData)

/-- At most n+1 list constructors are inspected, including the terminal test. -/
def test {A : Type} : Nat → List A → Bool × Nat
  | 0, [] => (true, 1)
  | 0, _ :: _ => (false, 1)
  | _ + 1, [] => (false, 1)
  | n + 1, _ :: xs => let r := test n xs; (r.1, r.2 + 1)

theorem test_value {A : Type} (n : Nat) (xs : List A) :
    (test n xs).1 = decide (xs.length = n) := by
  induction n generalizing xs with
  | zero => cases xs <;> simp [test]
  | succ n ih => cases xs <;> simp [test, ih]

theorem test_cost {A : Type} (n : Nat) (xs : List A) :
    (test n xs).2 ≤ n + 1 := by
  induction n generalizing xs with
  | zero => cases xs <;> simp [test]
  | succ n ih =>
    cases xs with
    | nil => simp [test]
    | cons x xs => exact Nat.add_le_add_right (ih xs) 1

def parse (tag : Byte) (width : Nat) (input : List Byte) :
    Option LeafData × Nat :=
  let data := (input.drop 2 |>.take width, input.drop (2 + width))
  let packed := test width data.1
  if packed.1 = true then
    let salt := test 32 data.2
    (if salt.1 = true ∧ BinMerkle32Leaf.leafInput tag data.1 data.2 = input
      then some data else none, packed.2 + salt.2)
  else (none, packed.2)

theorem parse_value (tag : Byte) (width : Nat) (input : List Byte) :
    (parse tag width input).1 = BinMerkleLeafCodec.parse tag width input := by
  simp only [parse, test_value, decide_eq_true_eq, BinMerkleLeafCodec.parse]
  by_cases hp : ((input.drop 2).take width).length = width <;>
    simp only [hp, if_true, if_false, true_and, false_and]

theorem parse_length_test_cost (tag : Byte) (width : Nat) (input : List Byte) :
    (parse tag width input).2 ≤ width + 34 := by
  have hp := test_cost width ((input.drop 2).take width)
  have hs := test_cost 32 (input.drop (2 + width))
  unfold parse
  dsimp only
  split <;> dsimp only <;> omega

#print axioms test_value
#print axioms test_cost
#print axioms parse_value
#print axioms parse_length_test_cost
end AspisR1.BinLeafBoundedLength
