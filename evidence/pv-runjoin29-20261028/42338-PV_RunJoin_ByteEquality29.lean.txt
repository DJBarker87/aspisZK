import AspisR1TerminalDecoder.Funs
import R1Z.BuilderRecordsArray
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ByteEquality29
open Aeneas Aeneas.Std Result

def compare (p : U8 × U8) : Result Bool := do
  let b ← core.cmp.PartialEq.ne.trait_default core.cmp.PartialEqU8 p.1 p.2
  ok (decide (¬ b = true))

theorem compare_result (a b : U8) : compare (a,b) = ok (decide (a=b)) := by
  simp [compare,core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEqU8]
#print axioms compare_result

theorem list_result (xs ys : List U8) (hl : xs.length=ys.length) :
    List.allM compare (xs.zip ys) = ok (decide (xs=ys)) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [List.allM]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have ht : xs.length=ys.length := by simpa using hl
      by_cases he : x=y
      · subst y
        simp [List.allM,compare_result,ih ys ht]
      · simp [List.allM,compare_result,he]
#print axioms list_result

theorem array_result {n : Usize} (a b : Array U8 n) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b = ok (decide (a=b)) := by
  rw [core.array.equality.PartialEqArray.eq,if_pos rfl]
  change List.allM compare (a.val.zip b.val) = _
  rw [list_result a.val b.val (by rw [a.property,b.property])]
  have he : a.val=b.val ↔ a=b := ⟨Subtype.ext,fun h => congrArg (fun x => x.val) h⟩
  rw [propext he]
#print axioms array_result
end R1Z.PV_RunJoin_ByteEquality29
