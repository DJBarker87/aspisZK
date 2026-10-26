import BinLeafBoundedLength

/-! List-work instrumentation. A list-constructor test, a copied list cell,
and a byte comparison each cost one unit. Arithmetic, pair/option allocation,
reference representation and surrounding extractor work are separate. -/
set_option autoImplicit false
namespace AspisR1.BinLeafListWork
open BinMerkle32Path
open BinMerkleLeafRecovery (LeafData)

def drop {A : Type} : Nat → List A → List A × Nat
  | 0, xs => (xs, 1)
  | _ + 1, [] => ([], 1)
  | n + 1, _ :: xs => let r := drop n xs; (r.1, r.2 + 1)

theorem drop_value {A : Type} (n : Nat) (xs : List A) :
    (drop n xs).1 = xs.drop n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => cases xs <;> simp only [drop, List.drop_succ_cons, ih, List.drop_nil]

theorem drop_work {A : Type} (n : Nat) (xs : List A) :
    (drop n xs).2 ≤ n + 1 := by
  induction n generalizing xs with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    cases xs with
    | nil => simp [drop]
    | cons x xs => exact Nat.add_le_add_right (ih xs) 1

def take {A : Type} : Nat → List A → List A × Nat
  | 0, _ => ([], 1)
  | _ + 1, [] => ([], 1)
  | n + 1, x :: xs => let r := take n xs; (x :: r.1, r.2 + 2)

theorem take_value {A : Type} (n : Nat) (xs : List A) :
    (take n xs).1 = xs.take n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => cases xs <;> simp only [take, List.take_succ_cons, ih, List.take_nil]

theorem take_work {A : Type} (n : Nat) (xs : List A) :
    (take n xs).2 ≤ 2 * n + 1 := by
  induction n generalizing xs with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    cases xs with
    | nil => simp [take]
    | cons x xs =>
      have h := ih xs
      change (take n xs).2 + 2 ≤ _
      omega

def append {A : Type} : List A → List A → List A × Nat
  | [], ys => (ys, 1)
  | x :: xs, ys => let r := append xs ys; (x :: r.1, r.2 + 2)

theorem append_value {A : Type} (xs ys : List A) :
    (append xs ys).1 = xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [append, ih, List.cons_append]

theorem append_work {A : Type} (xs ys : List A) :
    (append xs ys).2 = 2 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [append, ih, List.length_cons]; omega

/-- Equality visits at most the fixed left prefix, including a terminal
constructor test; no traversal of an arbitrary right suffix occurs. -/
def equal : List Byte → List Byte → Bool × Nat
  | [], [] => (true, 1)
  | [], _ :: _ => (false, 1)
  | _ :: _, [] => (false, 1)
  | x :: xs, y :: ys =>
    if x = y then let r := equal xs ys; (r.1, r.2 + 2)
    else (false, 2)

theorem equal_value (xs ys : List Byte) :
    (equal xs ys).1 = decide (xs = ys) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [equal]
  | cons x xs ih =>
    cases ys with
    | nil => simp [equal]
    | cons y ys => by_cases h : x = y <;> simp [equal, h, ih]

theorem equal_work (xs ys : List Byte) :
    (equal xs ys).2 ≤ 2 * xs.length + 1 := by
  induction xs generalizing ys with
  | nil => cases ys <;> exact Nat.le_refl _
  | cons x xs ih =>
    cases ys with
    | nil => simp [equal]
    | cons y ys =>
      have ht := ih ys
      by_cases h : x = y <;> simp only [equal, h, if_true, if_false, List.length_cons] <;>
        omega

def parse (tag : Byte) (width : Nat) (input : List Byte) : Option LeafData × Nat :=
  let d := drop 2 input
  let p := take width d.1
  let s := drop (2 + width) input
  let packed := BinLeafBoundedLength.test width p.1
  let prefixCost := d.2 + p.2 + s.2 + packed.2
  if packed.1 = true then
    let salt := BinLeafBoundedLength.test 32 s.1
    if salt.1 = true then
      let encoding := append p.1 s.1
      let eq := equal (0x10 :: tag :: encoding.1) input
      (if eq.1 = true then some (p.1, s.1) else none,
        prefixCost + salt.2 + encoding.2 + 2 + eq.2)
    else (none, prefixCost + salt.2)
  else (none, prefixCost)

theorem parse_value (tag : Byte) (width : Nat) (input : List Byte) :
    (parse tag width input).1 = BinMerkleLeafCodec.parse tag width input := by
  simp only [parse, drop_value, take_value, append_value, equal_value,
    BinLeafBoundedLength.test_value, decide_eq_true_eq,
    BinMerkleLeafCodec.parse, BinMerkle32Leaf.leafInput]
  by_cases hp : ((input.drop 2).take width).length = width <;>
    by_cases hs : (input.drop (2 + width)).length = 32 <;>
    simp only [hp, hs, true_and, false_and, if_true, if_false]

/-- Uniform in arbitrary input byte length, even on rejected inputs. -/
theorem parse_work (tag : Byte) (width : Nat) (input : List Byte) :
    (parse tag width input).2 ≤ 8 * width + 120 := by
  have hd := drop_work 2 input
  have hp := take_work width (drop 2 input).1
  have hs := drop_work (2 + width) input
  have ht := BinLeafBoundedLength.test_cost width (take width (drop 2 input).1).1
  have hu := BinLeafBoundedLength.test_cost 32 (drop (2 + width) input).1
  have hplen : (take width (drop 2 input).1).1.length ≤ width := by
    rw [take_value]
    exact List.length_take_le _ _
  have ha := append_work (take width (drop 2 input).1).1 (drop (2 + width) input).1
  unfold parse
  dsimp only
  split
  · split
    · have hpacked : (take width (drop 2 input).1).1.length = width := by
        have h := BinLeafBoundedLength.test_value width (take width (drop 2 input).1).1
        rename_i hp0 hs0
        rw [hp0] at h
        exact of_decide_eq_true h.symm
      have hsalt : (drop (2 + width) input).1.length = 32 := by
        have h := BinLeafBoundedLength.test_value 32 (drop (2 + width) input).1
        rename_i hp0 hs0
        rw [hs0] at h
        exact of_decide_eq_true h.symm
      have he := equal_work
        (0x10 :: tag :: (append (take width (drop 2 input).1).1 (drop (2 + width) input).1).1) input
      rw [List.length_cons, List.length_cons, append_value, List.length_append,
        hpacked, hsalt] at he
      dsimp only
      rw [append_value]
      omega
    · dsimp only; omega
  · dsimp only; omega

#print axioms drop_value
#print axioms drop_work
#print axioms take_value
#print axioms take_work
#print axioms append_value
#print axioms append_work
#print axioms equal_value
#print axioms equal_work
#print axioms parse_value
#print axioms parse_work
end AspisR1.BinLeafListWork
