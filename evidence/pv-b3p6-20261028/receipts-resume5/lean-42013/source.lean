import Aeneas.Std
namespace PV_B3P_Mask227
set_option autoImplicit false

def trailing : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, value => if value % 2 = 0 then 1 + trailing n (value / 2) else 0

def walk : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, mask => if mask = 0 then [] else trailing 16 mask :: walk n (mask &&& (mask-1))

def popcount (mask : Nat) : Nat := ((List.range 16).filter (fun i => mask.testBit i)).length

def foldResult {α : Type} (add : α → Nat → Aeneas.Std.Result α) : List Nat → α → Aeneas.Std.Result α
  | [], initial => .ok initial
  | index::tail, initial => do
    let next ← add initial index
    foldResult add tail next

theorem walk_1749 : walk 16 1749 = [0,2,4,6,7,9,10] := by decide
theorem complement_off_1749 : popcount 1749 ≤ 8 := by decide
theorem sum_1749 {α : Type} (zero : α) (add : α → α → α) (values : Nat → α) :
    (walk 16 1749).foldl (fun sum index => add sum (values index)) zero = add (add (add (add (add (add (add (zero) (values 0)) (values 2)) (values 4)) (values 6)) (values 7)) (values 9)) (values 10) := by
  rw [walk_1749]
  rfl
theorem result_1749 {α : Type} (zero : α) (add : α → Nat → Aeneas.Std.Result α) :
    foldResult add (walk 16 1749) zero = (    do
      let next0 ← add zero 0
      let next1 ← add next0 2
      let next2 ← add next1 4
      let next3 ← add next2 6
      let next4 ← add next3 7
      let next5 ← add next4 9
      let next6 ← add next5 10
      .ok next6) := by
  rw [walk_1749]
  rfl
#print axioms walk_1749
#print axioms complement_off_1749
#print axioms sum_1749
#print axioms result_1749
theorem walk_2048 : walk 16 2048 = [11] := by decide
theorem complement_off_2048 : popcount 2048 ≤ 8 := by decide
theorem sum_2048 {α : Type} (zero : α) (add : α → α → α) (values : Nat → α) :
    (walk 16 2048).foldl (fun sum index => add sum (values index)) zero = add (zero) (values 11) := by
  rw [walk_2048]
  rfl
theorem result_2048 {α : Type} (zero : α) (add : α → Nat → Aeneas.Std.Result α) :
    foldResult add (walk 16 2048) zero = (    do
      let next0 ← add zero 11
      .ok next0) := by
  rw [walk_2048]
  rfl
#print axioms walk_2048
#print axioms complement_off_2048
#print axioms sum_2048
#print axioms result_2048
theorem walk_2049 : walk 16 2049 = [0,11] := by decide
theorem complement_off_2049 : popcount 2049 ≤ 8 := by decide
theorem sum_2049 {α : Type} (zero : α) (add : α → α → α) (values : Nat → α) :
    (walk 16 2049).foldl (fun sum index => add sum (values index)) zero = add (add (zero) (values 0)) (values 11) := by
  rw [walk_2049]
  rfl
theorem result_2049 {α : Type} (zero : α) (add : α → Nat → Aeneas.Std.Result α) :
    foldResult add (walk 16 2049) zero = (    do
      let next0 ← add zero 0
      let next1 ← add next0 11
      .ok next1) := by
  rw [walk_2049]
  rfl
#print axioms walk_2049
#print axioms complement_off_2049
#print axioms sum_2049
#print axioms result_2049
theorem walk_4097 : walk 16 4097 = [0,12] := by decide
theorem complement_off_4097 : popcount 4097 ≤ 8 := by decide
theorem sum_4097 {α : Type} (zero : α) (add : α → α → α) (values : Nat → α) :
    (walk 16 4097).foldl (fun sum index => add sum (values index)) zero = add (add (zero) (values 0)) (values 12) := by
  rw [walk_4097]
  rfl
theorem result_4097 {α : Type} (zero : α) (add : α → Nat → Aeneas.Std.Result α) :
    foldResult add (walk 16 4097) zero = (    do
      let next0 ← add zero 0
      let next1 ← add next0 12
      .ok next1) := by
  rw [walk_4097]
  rfl
#print axioms walk_4097
#print axioms complement_off_4097
#print axioms sum_4097
#print axioms result_4097
theorem walk_6144 : walk 16 6144 = [11,12] := by decide
theorem complement_off_6144 : popcount 6144 ≤ 8 := by decide
theorem sum_6144 {α : Type} (zero : α) (add : α → α → α) (values : Nat → α) :
    (walk 16 6144).foldl (fun sum index => add sum (values index)) zero = add (add (zero) (values 11)) (values 12) := by
  rw [walk_6144]
  rfl
theorem result_6144 {α : Type} (zero : α) (add : α → Nat → Aeneas.Std.Result α) :
    foldResult add (walk 16 6144) zero = (    do
      let next0 ← add zero 11
      let next1 ← add next0 12
      .ok next1) := by
  rw [walk_6144]
  rfl
#print axioms walk_6144
#print axioms complement_off_6144
#print axioms sum_6144
#print axioms result_6144
theorem walk_6145 : walk 16 6145 = [0,11,12] := by decide
theorem complement_off_6145 : popcount 6145 ≤ 8 := by decide
theorem sum_6145 {α : Type} (zero : α) (add : α → α → α) (values : Nat → α) :
    (walk 16 6145).foldl (fun sum index => add sum (values index)) zero = add (add (add (zero) (values 0)) (values 11)) (values 12) := by
  rw [walk_6145]
  rfl
theorem result_6145 {α : Type} (zero : α) (add : α → Nat → Aeneas.Std.Result α) :
    foldResult add (walk 16 6145) zero = (    do
      let next0 ← add zero 0
      let next1 ← add next0 11
      let next2 ← add next1 12
      .ok next2) := by
  rw [walk_6145]
  rfl
#print axioms walk_6145
#print axioms complement_off_6145
#print axioms sum_6145
#print axioms result_6145
theorem walk_26214 : walk 16 26214 = [1,2,5,6,9,10,13,14] := by decide
theorem complement_off_26214 : popcount 26214 ≤ 8 := by decide
theorem sum_26214 {α : Type} (zero : α) (add : α → α → α) (values : Nat → α) :
    (walk 16 26214).foldl (fun sum index => add sum (values index)) zero = add (add (add (add (add (add (add (add (zero) (values 1)) (values 2)) (values 5)) (values 6)) (values 9)) (values 10)) (values 13)) (values 14) := by
  rw [walk_26214]
  rfl
theorem result_26214 {α : Type} (zero : α) (add : α → Nat → Aeneas.Std.Result α) :
    foldResult add (walk 16 26214) zero = (    do
      let next0 ← add zero 1
      let next1 ← add next0 2
      let next2 ← add next1 5
      let next3 ← add next2 6
      let next4 ← add next3 9
      let next5 ← add next4 10
      let next6 ← add next5 13
      let next7 ← add next6 14
      .ok next7) := by
  rw [walk_26214]
  rfl
#print axioms walk_26214
#print axioms complement_off_26214
#print axioms sum_26214
#print axioms result_26214

def sourceMasks : List Nat := [6144,6144,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6144,4097,2048,6145,2049,2048,6145,2049,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,4097,6145,6145,4097,26214,26214,26214,26214,26214,26214,1749]
def reachedMasks : List Nat := [1749,2048,2049,4097,6144,6145,26214]
theorem table_masks : ∀ mask ∈ sourceMasks, mask ∈ reachedMasks := by decide
#print axioms table_masks
end PV_B3P_Mask227
