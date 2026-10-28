import PV_B3P_GuardedWords226V3
namespace PV_B3P_AppendFields226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_RustResult PV_B3P_ByteLayout226V3
set_option autoImplicit false
abbrev E := PV_B3P_GuardedWords226V3.E

def appendSegments (out : List U8) :
    List (Result (core.result.Result (List U8) E)) →
    Result (core.result.Result (List U8) E)
  | [] => .ok (.Ok out)
  | x::xs => bindR x (fun bytes => appendSegments (out++bytes) xs)

theorem append_segments_value (xs : List (Result (core.result.Result (List U8) E)))
    (out : List U8) : appendSegments out xs =
    mapR (fun segments => out ++ segments.flatten) (collect xs) := by
  induction xs generalizing out with
  | nil => simp [appendSegments,collect,mapR,bindR]
  | cons x xs ih =>
    simp only [appendSegments,collect,mapR]
    rw [bindR_assoc]
    cases x with
    | fail e => rfl
    | div => rfl
    | ok inner =>
      cases inner with
      | Err e => rfl
      | Ok bytes =>
        simp only [bindR]
        rw [ih]
        cases h : collect xs with
        | fail e => rfl
        | div => rfl
        | ok inner =>
          cases inner with
          | Err e => rfl
          | Ok segments =>
            simp only [mapR,bindR,List.flatten_cons,List.append_assoc]

def nativeFields (out : List U8) : List U32 →
    Result (core.result.Result (List U8) E)
  | [] => .ok (.Ok out)
  | v::xs => if v < 2147483647#u32 then
      nativeFields (out++wordBytes v) xs
    else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public)

theorem native_fields_complete (out : List U8) (xs : List U32) :
    nativeFields out xs =
      if xs.all (fun v => decide (v < 2147483647#u32)) then
        .ok (.Ok (out++fields xs))
      else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public) := by
  induction xs generalizing out with
  | nil => simp [nativeFields,fields]
  | cons v xs ih =>
    simp only [nativeFields,List.all_cons]
    by_cases hc : v < 2147483647#u32
    · simp only [hc,↓reduceIte,decide_true,Bool.true_and]
      rw [ih]
      cases h : xs.all (fun v => decide (v < 2147483647#u32)) <;>
        simp only [h,Bool.false_eq_true,↓reduceIte,fields,List.flatMap_cons,List.append_assoc]
    · simp only [hc,↓reduceIte,decide_false,Bool.false_and,Bool.false_eq_true]

theorem repeated_byte_checks (out : List U8) (xs : List U32) :
    nativeFields out xs = mapR (fun bytes => out++bytes)
      (mapR List.flatten (collect (xs.map PV_B3P_WordLaw226V3.four))) := by
  rw [native_fields_complete,PV_B3P_GuardedWords226V3.complete_byte_fields]
  cases h : xs.all (fun v => decide (v < 2147483647#u32)) <;>
    simp only [h,Bool.false_eq_true,↓reduceIte,mapR,bindR]

#print axioms append_segments_value
#print axioms native_fields_complete
#print axioms repeated_byte_checks
end PV_B3P_AppendFields226
