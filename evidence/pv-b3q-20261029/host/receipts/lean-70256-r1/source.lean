import PV_B3Q_SliceSuffix
namespace PV_B3Q_SliceEqualityValue
open Aeneas Aeneas.Std PV_B3Q_SliceEqual PV_B3Q_SliceSuffix PV_B3P_Groups14227
set_option autoImplicit false
def scalar_ne (x y : U32) : Result Bool := .ok (decide (x≠y))
theorem tail_value (left right : List U32) (same : left.length=right.length) :
    tail_loop scalar_ne left.length left right = .ok (decide (left=right)) := by
 induction left generalizing right with
 | nil =>
   cases right with
   | nil => rfl
   | cons y ys => simp only [List.length_nil,List.length_cons] at same; omega
 | cons x xs ih =>
   cases right with
   | nil => simp only [List.length_nil,List.length_cons] at same; omega
   | cons y ys =>
     have lengths : xs.length=ys.length := Nat.succ.inj same
     by_cases equal : x=y
     · subst y
       simp [tail_loop,scalar_ne,ih ys lengths]
     · simp [tail_loop,scalar_ne,equal]
/-- Complete value law for the source while-loop, including the initial unequal
length return and every possible first unequal element. -/
theorem source_value (left right : List U32) :
    PV_B3Q_SliceEqual.source scalar_ne left right = .ok (decide (left=right)) := by
 by_cases same : left.length=right.length
 · unfold PV_B3Q_SliceEqual.source
   simp only [same,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
   rw [loop_suffix_binding]
   exact tail_value left right same
 · have different : left≠right := fun h => same (congrArg List.length h)
   simp [PV_B3Q_SliceEqual.source,same,different]
/-- Concrete M31/U32 slice comparison family; primitive comparison is a
separate catalogue row, with no hidden failing comparator assumption. -/
theorem slice_value_link : PV_B3P_Link_std_dependency_closure14
    (fun _ : Unit => List U32 → List U32 → Result Bool)
    (fun _ => PV_B3Q_SliceEqual.source scalar_ne)
    (fun _ left right => .ok (decide (left=right))) := by
 intro _
 funext left right
 exact source_value left right
#print axioms tail_value
#print axioms source_value
#print axioms slice_value_link
end PV_B3Q_SliceEqualityValue
