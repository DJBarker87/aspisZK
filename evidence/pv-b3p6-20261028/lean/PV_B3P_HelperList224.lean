import PV_B3P_HelperPlan224
namespace PV_B3P_HelperList224
open Aeneas Aeneas.Std PV_B3P_RustResult PV_B3P_HelperPlan224
set_option autoImplicit false

theorem prefix_set {F : Type} (out : List F) (r : Nat) (value : F) (hr : r < out.length) :
    (out.set r value).take (r+1) = out.take r ++ [value] := by
  rw [List.take_succ_eq_append_getElem (by simpa using hr),List.take_set_of_le (by omega),List.getElem_set_self]


def ordered {F E : Type} (eval : Nat → Result (core.result.Result F E)) (r n : Nat) :=
  collect ((List.range' r n).map eval)

theorem ordered_step {F E : Type} (eval : Nat → Result (core.result.Result F E)) (r n : Nat) :
    ordered eval r (n+1) = bindR (eval r) (fun value => mapR (fun tail => value::tail) (ordered eval (r+1) n)) := by
  simp only [ordered,List.range'_succ,List.map_cons,collect,mapR]

theorem map_map {F G H E : Type} (x : Result (core.result.Result F E)) (f : F → G) (g : G → H) :
    mapR g (mapR f x) = mapR (fun a => g (f a)) x := by
  cases x with
  | fail e => rfl
  | div => rfl
  | ok v => cases v <;> rfl

theorem map_id {F E : Type} (x : Result (core.result.Result F E)) : mapR id x = x := by
  cases x with
  | fail e => rfl
  | div => rfl
  | ok v => cases v <;> rfl

-- The buffer implementation has exactly the independent ordered-value law,
-- including all rejection, runtime-failure and divergence channels.
theorem fill {F E : Type} (eval : Nat → Result (core.result.Result F E))
    (r n : Nat) (out : List F) (hcap : r+n ≤ out.length) :
    run eval r n out = mapR (fun values => out.take r ++ values ++ out.drop (r+n)) (ordered eval r n) := by
  induction n generalizing r out with
  | zero => simp [run,ordered,collect,mapR,bindR]
  | succ n ih =>
    have hr : r < out.length := by omega
    rw [run,ordered_step]
    cases he : eval r with
    | fail e => rfl
    | div => rfl
    | ok res =>
      cases res with
      | Err e => rfl
      | Ok value =>
        simp only [bindR]
        rw [ih (r+1) (out.set r value) (by simp only [List.length_set]; omega),map_map]
        apply congrArg (fun f => mapR f (ordered eval (r+1) n))
        funext tail
        rw [prefix_set out r value hr,List.drop_set_of_lt (by omega)]
        simp only [List.append_assoc,List.singleton_append]
        congr 2 <;> omega

theorem whole {F E : Type} (eval : Nat → Result (core.result.Result F E)) (out : List F) :
    run eval 0 out.length out = ordered eval 0 out.length := by
  rw [fill eval 0 out.length out (by omega)]
  simp only [List.take_zero,List.nil_append,Nat.zero_add,List.drop_length,List.append_nil]
  exact map_id _

#print axioms prefix_set
#print axioms ordered_step
#print axioms map_map
#print axioms map_id
#print axioms fill
#print axioms whole
end PV_B3P_HelperList224
