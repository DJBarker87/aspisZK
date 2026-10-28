import PV_B3P_NativeSteps226
namespace PV_B3P_NativeList226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_RustResult PV_B3P_ByteLayout226V3 PV_B3P_NativeSteps226
set_option autoImplicit false

def contents : Step → List U8
  | .push b => [b]
  | .bytes s => s.val
  | .fields xs => fields xs

def guard : Step → Bool
  | .push _ => true
  | .bytes _ => true
  | .fields xs => xs.all (fun v => decide (v < 2147483647#u32))

def payload : List Step → List U8
  | [] => []
  | x::xs => contents x ++ payload xs

def valid : List Step → Bool
  | [] => true
  | x::xs => guard x && valid xs

theorem payload_length (xs : List Step) : (payload xs).length = budget xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x <;> simp only [payload,contents,List.length_append,List.length_cons,List.length_nil,
      fields_length,ih,budget,width]

set_option backward.isDefEq.respectTransparency false in
theorem complete_result (out : List U8) (xs : List Step) :
    runList out xs = if valid xs then .ok (.Ok (out ++ payload xs))
      else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public) := by
  induction xs generalizing out with
  | nil => simp only [runList,valid,payload,↓reduceIte,List.append_nil]
  | cons x xs ih =>
    cases x with
    | push b =>
      rw [runList,ih]
      cases hv : valid xs <;>
        simp only [valid,guard,Bool.true_and,payload,contents,hv,Bool.false_eq_true,↓reduceIte,List.append_assoc]
    | bytes s =>
      rw [runList,ih]
      cases hv : valid xs <;>
        simp only [valid,guard,Bool.true_and,payload,contents,hv,Bool.false_eq_true,↓reduceIte,List.append_assoc]
    | fields fs =>
      rw [runList,PV_B3P_AppendFields226.native_fields_complete]
      cases hg : fs.all (fun v => decide (v < 2147483647#u32)) <;>
        simp only [hg,Bool.false_eq_true,↓reduceIte,bindR,valid,guard,Bool.false_and,Bool.true_and,payload,contents]
      rw [ih]
      cases hv : valid xs <;> simp only [hv,Bool.false_eq_true,↓reduceIte,List.append_assoc]

#print axioms payload_length
#print axioms complete_result
end PV_B3P_NativeList226
