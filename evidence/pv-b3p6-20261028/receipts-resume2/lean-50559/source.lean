import PV_B3P_NativeFieldsVec226
namespace PV_B3P_NativeGroups226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_RustResult
set_option autoImplicit false
abbrev E := aspis_core.state_only_prefix.r0.Error
set_option backward.isDefEq.respectTransparency false in
theorem fields_append (out : alloc.vec.Vec U8) (xs ys : List U32) :
    bindR (PV_B3P_NativeFieldsVec226.fieldsVec out xs)
      (fun out' => PV_B3P_NativeFieldsVec226.fieldsVec out' ys) =
    PV_B3P_NativeFieldsVec226.fieldsVec out (xs++ys) := by
  induction xs generalizing out with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append,PV_B3P_NativeFieldsVec226.fieldsVec]
    by_cases hc : x < 2147483647#u32
    · simp only [hc,↓reduceIte]
      rw [bindR_outer]
      congr 1
      funext out'
      exact ih out'
    · simp only [hc,↓reduceIte,bindR]

def groups (out : alloc.vec.Vec U8) : List (List U32) →
    Result (core.result.Result (alloc.vec.Vec U8) E)
  | [] => .ok (.Ok out)
  | xs::rest => bindR (PV_B3P_NativeFieldsVec226.fieldsVec out xs) (fun out' => groups out' rest)

theorem complete_result (out : alloc.vec.Vec U8) (rows : List (List U32)) :
    groups out rows = PV_B3P_NativeFieldsVec226.fieldsVec out rows.flatten := by
  induction rows generalizing out with
  | nil => rfl
  | cons xs rows ih =>
    simp only [groups,List.flatten_cons]
    simp only [ih,fields_append]

#print axioms fields_append
#print axioms complete_result
end PV_B3P_NativeGroups226
