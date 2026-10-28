import PV_B3P_WordLaw226V3
namespace PV_B3P_GuardedWords226V3
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_RustResult PV_B3P_ByteLayout226V3
set_option autoImplicit false
abbrev E := aspis_core.state_only_prefix.r0.Error

def wordResult (v : U32) : Result (core.result.Result (List U8) E) :=
  if v < 2147483647#u32 then .ok (.Ok (wordBytes v))
  else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public)

theorem complete_words (xs : List U32) :
    collect (xs.map wordResult) =
      if xs.all (fun v => decide (v < 2147483647#u32)) then
        .ok (.Ok (xs.map wordBytes))
      else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public) := by
  induction xs with
  | nil => rfl
  | cons v xs ih =>
    simp only [List.map_cons,collect,List.all_cons,wordResult]
    by_cases hc : v < 2147483647#u32
    · simp only [hc,↓reduceIte,decide_true,Bool.true_and,bindR]
      rw [ih]
      cases hp : xs.all (fun v => decide (v < 2147483647#u32)) <;> rfl
    · simp only [hc,↓reduceIte,decide_false,Bool.false_and,bindR]

theorem complete_byte_fields (xs : List U32) :
    mapR List.flatten (collect (xs.map PV_B3P_WordLaw226V3.four)) =
      if xs.all (fun v => decide (v < 2147483647#u32)) then
        .ok (.Ok (fields xs))
      else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public) := by
  have hm : xs.map PV_B3P_WordLaw226V3.four = xs.map wordResult := by
    congr 1
    funext v
    exact PV_B3P_WordLaw226V3.complete_word v
  rw [hm,complete_words]
  cases hp : xs.all (fun v => decide (v < 2147483647#u32)) <;>
    simp only [hp,Bool.false_eq_true,↓reduceIte,mapR,bindR,fields] <;> rfl

#print axioms complete_words
#print axioms complete_byte_fields
end PV_B3P_GuardedWords226V3
