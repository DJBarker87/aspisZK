import NKM_Roots
set_option autoImplicit false
noncomputable section
namespace NKM_Trace
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase AspisV8R19
open NKM_circle NKM_FieldLaws NKM_CircleModel
structure Event where
 kind : Nat
 a : NKM_circle.field.QM31
 b : NKM_circle.field.QM31
 out : Option NKM_circle.field.QM31

def run (t : NKM_circle.field.QM31) : Result (NKM_Roots.Reply × List Event) := do
 let s ← NKM_circle.field.QM31.square t
 let d ← NKM_circle.field.QM31.add NKM_circle.field.QM31.ONE s
 let i ← NKM_circle.field.QM31.try_inv d
 let prefix := [Event.mk 0 t t (some s),Event.mk 1 NKM_circle.field.QM31.ONE s (some d),Event.mk 2 d NKM_circle.field.QM31.ZERO i]
 match i with
 | none => ok (.Err .SingularParameter,prefix)
 | some inv =>
  let n ← NKM_circle.field.QM31.sub NKM_circle.field.QM31.ONE s
  let x ← NKM_circle.field.QM31.mul n inv
  let two ← NKM_circle.field.QM31.add t t
  let y ← NKM_circle.field.QM31.mul two inv
  ok (.Ok ⟨x,y⟩,prefix++[Event.mk 3 NKM_circle.field.QM31.ONE s (some n),Event.mk 4 n inv (some x),Event.mk 1 t t (some two),Event.mk 4 two inv (some y)])

def events (t : QM31Exact) : List Event :=
 let d:=1+t*t
 let inv:=encode d⁻¹
 [Event.mk 0 (encode t) (encode t) (some (encode (t*t))),
  Event.mk 1 (encode 1) (encode (t*t)) (some (encode d)),
  Event.mk 2 (encode d) (encode 0) (if d=0 then none else some inv)] ++
 if d=0 then [] else
 [Event.mk 3 (encode 1) (encode (t*t)) (some (encode (1-t*t))),
  Event.mk 4 (encode (1-t*t)) inv (some (encode ((1-t*t)*d⁻¹))),
  Event.mk 1 (encode t) (encode t) (some (encode (t+t))),
  Event.mk 4 (encode (t+t)) inv (some (encode ((t+t)*d⁻¹)))]

theorem complete (t : QM31Exact) : run (encode t)=ok (circleResult t,events t) := by
 by_cases hd : 1+t*t=0
 · simp only [run,square,one,add,hd,inverse_zero,bind_tc_ok,events,circleResult,if_true,zero,List.append_nil]
 · simp only [run,square,one,add,inverse_nonzero _ hd,bind_tc_ok,sub,mul,events,circleResult,hd,if_false,point,zero]

theorem erased (t : QM31Exact) :
 (do let r ← run (encode t);ok r.1)=NKM_circle.circle.secure_circle_point_from_parameter (encode t) := by
 rw [complete,circle_total];rfl

theorem count (t : QM31Exact) : (events t).length=if 1+t*t=0 then 3 else 7 := by
 by_cases hd : 1+t*t=0 <;> simp only [events,hd,if_true,if_false,List.length_append,List.length_cons,List.length_nil]

theorem singular_prefix (t : QM31Exact) (hd : 1+t*t=0) :
 (do let r ← run (encode t);ok (r.1,r.2.length))=ok (.Err .SingularParameter,3) := by
 rw [complete,count]
 simp only [bind_tc_ok,circleResult,hd,if_true]

#print axioms complete
#print axioms erased
#print axioms count
#print axioms singular_prefix
end NKM_Trace
end
