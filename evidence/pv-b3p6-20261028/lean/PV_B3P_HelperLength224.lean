import PV_B3P_HelperList224
namespace PV_B3P_HelperLength224
open Aeneas Aeneas.Std PV_B3P_RustResult
set_option autoImplicit false

theorem collect_length {F E : Type} (xs : List (Result (core.result.Result F E)))
    (out : List F) (h : collect xs = .ok (.Ok out)) : out.length = xs.length := by
  induction xs generalizing out with
  | nil => cases h; rfl
  | cons head tail ih =>
    cases head with
    | fail e => cases h
    | div => cases h
    | ok value =>
      cases value with
      | Err e => cases h
      | Ok value =>
        simp only [collect,bindR] at h
        cases ht : collect tail with
        | fail e => simp only [ht,bindR] at h; cases h
        | div => simp only [ht,bindR] at h; cases h
        | ok rest =>
          cases rest with
          | Err e => simp only [ht,bindR] at h; cases h
          | Ok rest =>
            simp only [ht,bindR] at h
            cases h
            simp only [List.length_cons,ih rest ht]

theorem ordered_length {F E : Type} (eval : Nat → Result (core.result.Result F E))
    (r n : Nat) (out : List F)
    (h : PV_B3P_HelperList224.ordered eval r n = .ok (.Ok out)) : out.length = n := by
  have hl := collect_length _ out h
  simpa only [List.length_map,List.length_range'] using hl

#print axioms collect_length
#print axioms ordered_length
end PV_B3P_HelperLength224
