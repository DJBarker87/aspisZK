import NJB_StateUpdates
set_option autoImplicit false
namespace AspisR1.NJB_AbortPrefix
open Aeneas Aeneas.Std Result
variable {I α : Type} [DecidableEq I]
open FIv_NativeArithmetic (NQ)
abbrev State := I → NQ
theorem append (step : α → State → Result State) (prefix suffix : List α) (s : State) :
 NJB_StateUpdates.run step (prefix++suffix) s=
 (do let mid ← NJB_StateUpdates.run step prefix s;NJB_StateUpdates.run step suffix mid) := by
 induction prefix generalizing s with
 | nil => rfl
 | cons x xs ih =>
  simp only [List.cons_append,NJB_StateUpdates.run]
  cases h : step x s <;> simp only [h,bind_tc_ok,bind_tc_fail,bind_tc_div,ih]
/-- Generic abort-prefix support, not a positive row root. A concrete parent
must discharge both child Results itself, at the same observed call. -/
theorem fail (step : α → State → Result State) (prefix suffix : List α) (x : α) (s mid : State)
 (error : Error) (before : NJB_StateUpdates.run step prefix s=ok mid) (abort : step x mid=Result.fail error) :
 NJB_StateUpdates.run step (prefix++x::suffix) s=Result.fail error := by
 rw [append,before]
 simp only [bind_tc_ok,NJB_StateUpdates.run,abort,bind_tc_fail]
theorem div (step : α → State → Result State) (prefix suffix : List α) (x : α) (s mid : State)
 (before : NJB_StateUpdates.run step prefix s=ok mid) (abort : step x mid=Result.div) :
 NJB_StateUpdates.run step (prefix++x::suffix) s=Result.div := by
 rw [append,before]
 simp only [bind_tc_ok,NJB_StateUpdates.run,abort,bind_tc_div]
#print axioms append
#print axioms fail
#print axioms div
end AspisR1.NJB_AbortPrefix
