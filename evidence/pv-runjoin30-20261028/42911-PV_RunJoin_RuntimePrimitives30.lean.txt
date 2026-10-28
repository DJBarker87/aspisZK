import R1Z.BuilderAdmissionCommon
import R1Z.PV_RunJoin_ByteEquality29
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RuntimePrimitives30
open Aeneas Aeneas.Std Result AspisBuilderAdmissionSource
local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev wordInst := aspis_core.field.M31.Insts.CoreCmpPartialEqM31

theorem word_eq (a b : U32) : wordInst.eq a b = ok (decide (a=b)) := rfl
#print axioms word_eq

theorem word_ne (a b : U32) :
    core.cmp.PartialEq.ne.trait_default wordInst a b = ok (decide (a≠b)) := by
  simp only [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,wordInst,aspis_core.field.M31.Insts.CoreCmpPartialEqM31,aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,bind_tc_ok]
  by_cases h : a=b <;> simp [h]
#print axioms word_ne

def compare : U32 × U32 → Result Bool
  | (a,b) => do
    let c ← wordInst.ne a b
    ok (decide (¬c=true))

theorem compare_result (a b : U32) : compare (a,b) = ok (decide (a=b)) := by
  change (do let c ← core.cmp.PartialEq.ne.trait_default wordInst a b
             ok (decide (¬c=true))) = _
  rw [word_ne]
  simp only [bind_tc_ok]
  by_cases h : a=b <;> simp [h]
#print axioms compare_result

theorem list_result (xs ys : List U32) (hl : xs.length=ys.length) :
    List.allM compare (xs.zip ys) = ok (decide (xs=ys)) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [List.allM] <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have ht : xs.length=ys.length := by simpa using hl
      by_cases he : x=y
      · subst y; simp [List.allM,compare_result,ih ys ht]
      · simp [List.allM,compare_result,he] <;> rfl
#print axioms list_result

theorem array_eq {n : Usize} (a b : Array U32 n) :
    core.array.equality.PartialEqArray.eq wordInst a b = ok (decide (a=b)) := by
  rw [core.array.equality.PartialEqArray.eq]
  have ha : a.length=n.val := by simp [Array.length,a.property]
  have hb : b.length=n.val := by simp [Array.length,b.property]
  rw [if_pos (ha.trans hb.symm)]
  change List.allM compare (a.val.zip b.val) = _
  rw [list_result a.val b.val (by rw [a.property,b.property])]
  have he : a.val=b.val ↔ a=b := ⟨Subtype.ext,fun h => congrArg (fun x => x.val) h⟩
  by_cases h : a=b
  · subst b; simp
  · have hv : ¬a.val=b.val := fun hv => h (he.mp hv)
    simp only [decide_eq_false hv,decide_eq_false h]
#print axioms array_eq

theorem array_ne {n : Usize} (a b : Array U32 n) :
    core.array.equality.PartialEqArray.ne wordInst a b = ok (decide (a≠b)) := by
  rw [core.array.equality.PartialEqArray.ne,array_eq]
  simp only [bind_tc_ok]
  by_cases h : a=b <;> simp [h]
#print axioms array_ne

theorem bytes_ne {n : Usize} (a b : Array U8 n) :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a b = ok (decide (a≠b)) := by
  rw [core.array.equality.PartialEqArray.ne,PV_RunJoin_ByteEquality29.array_result]
  simp only [bind_tc_ok]
  by_cases h : a=b <;> simp [h]
#print axioms bytes_ne

theorem list_contains {n : Usize} (x : Array U32 n) (xs : List (Array U32 n)) :
    List.anyM ((Array.Insts.CoreCmpPartialEqArray n wordInst).eq x) xs =
      ok (decide (x ∈ xs)) := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : x=y <;>
      simp [List.anyM,Array.Insts.CoreCmpPartialEqArray,array_eq,h,ih]
#print axioms list_contains

theorem contains {n : Usize} (s : Slice (Array U32 n)) (x : Array U32 n) :
    core.slice.Slice.contains (Array.Insts.CoreCmpPartialEqArray n wordInst) s x =
      ok (decide (x ∈ s.val)) := list_contains x s.val
#print axioms contains
end R1Z.PV_RunJoin_RuntimePrimitives30
