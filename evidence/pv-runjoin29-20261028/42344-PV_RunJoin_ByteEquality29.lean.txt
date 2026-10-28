import AspisR1TerminalDecoder.Funs
import R1Z.BuilderRecordsArray
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ByteEquality29
open Aeneas Aeneas.Std Result
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def compare : U8 × U8 → Result Bool
  | (x,y) => do
    let b ← core.cmp.PartialEqU8.ne x y
    ok (decide (¬ b = true))

theorem compare_result (a b : U8) : compare (a,b) = ok (decide (a=b)) := by
  simp [compare,core.cmp.PartialEqU8,core.cmp.impls.PartialEqU8.ne,liftFun2]
#print axioms compare_result

theorem list_result (xs ys : List U8) (hl : xs.length=ys.length) :
    List.allM compare (xs.zip ys) = ok (decide (xs=ys)) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [List.allM] <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have ht : xs.length=ys.length := by simpa using hl
      by_cases he : x=y
      · subst y
        simp [List.allM,compare_result,ih ys ht]
      · simp [List.allM,compare_result,he] <;> rfl
#print axioms list_result

theorem array_result {n : Usize} (a b : Array U8 n) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b = ok (decide (a=b)) := by
  rw [core.array.equality.PartialEqArray.eq]
  have ha : a.length=n.val := by simp [Array.length,a.property]
  have hb : b.length=n.val := by simp [Array.length,b.property]
  rw [if_pos (ha.trans hb.symm)]
  change List.allM compare (a.val.zip b.val) = _
  rw [list_result a.val b.val (by rw [a.property,b.property])]
  have he : a.val=b.val ↔ a=b := ⟨Subtype.ext,fun h => congrArg (fun x => x.val) h⟩
  rw [propext he]
#print axioms array_result
end R1Z.PV_RunJoin_ByteEquality29
