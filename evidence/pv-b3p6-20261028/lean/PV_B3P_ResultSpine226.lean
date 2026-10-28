import PV_B3P_ResultSuccess226
namespace PV_B3P_ResultSpine226
open Aeneas Aeneas.Std PV_B3P_RustResult
set_option autoImplicit false

theorem collect_append {α E : Type} (xs ys : List (Result (core.result.Result α E))) :
    collect (xs++ys) = bindR (collect xs)
      (fun headValues => mapR (fun tailValues => headValues++tailValues) (collect ys)) := by
  induction xs with
  | nil =>
    simp only [List.nil_append,collect,bindR,mapR]
    cases collect ys with
    | fail e => rfl
    | div => rfl
    | ok v => cases v <;> rfl
  | cons x xs ih =>
    simp only [List.cons_append,collect]
    rw [ih]
    cases x with
    | fail e => rfl
    | div => rfl
    | ok v =>
      cases v with
      | Err e => rfl
      | Ok a =>
        simp only [bindR,mapR]
        cases collect xs with
        | fail e => rfl
        | div => rfl
        | ok v =>
          cases v with
          | Err e => rfl
          | Ok headValues =>
            cases collect ys with
            | fail e => rfl
            | div => rfl
            | ok v => cases v <;> rfl

theorem collect_pure {α E : Type} (xs : List α) :
    collect (xs.map (fun a => (Result.ok (core.result.Result.Ok a) : Result (core.result.Result α E)))) =
      .ok (.Ok xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,collect,bindR,ih]

theorem padding {α E : Type} (xs : List (Result (core.result.Result α E))) (pad : List α) :
    mapR (fun ys => ys.take xs.length)
      (collect (xs ++ pad.map (fun a => .ok (.Ok a)))) = collect xs := by
  rw [collect_append,collect_pure]
  cases hx : collect xs with
  | fail e => rfl
  | div => rfl
  | ok v =>
    cases v with
    | Err e => rfl
    | Ok ys =>
      have hlen := PV_B3P_ResultSuccess226.collect_length xs ys hx
      simp only [mapR,bindR]
      rw [← hlen]
      simp only [List.take_append,List.take_length,Nat.sub_self,List.take_zero,List.append_nil]

#print axioms collect_append
#print axioms collect_pure
#print axioms padding
end PV_B3P_ResultSpine226
