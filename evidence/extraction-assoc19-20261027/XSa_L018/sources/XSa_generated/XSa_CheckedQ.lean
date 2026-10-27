import XSa_DotCarriers
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
namespace XSa_CheckedQ
open AspisR1EbyKCheckedQAllParamV1 AspisR1EbyKCheckedQConcreteAll

def valid (q : E.Q) : Bool :=
 q.c0.a<2147483647#u32 && q.c0.b<2147483647#u32 &&
 q.c1.a<2147483647#u32 && q.c1.b<2147483647#u32

def scalar (q : E.Q) : AspisR1EbyKPushDotBackend.PushQm :=
 ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

theorem checked (q : E.Q) : checkedQWithAll concreteAll (scalar q) =
 ok (if valid q then .Ok (XRn_Join_toQ q) else .Err ()) := by
 unfold checkedQWithAll limbsOf fromLimbsWithAll concreteAll
 simp only [bind_tc_ok,lift,Array.to_slice,Array.make,core.slice.Slice.iter,List.drop_zero]
 unfold allRun fromLimbsClosureFnMut fromLimbsClosureCallMut
 simp only [bind_tc_ok]
 unfold valid scalar P
 split_ifs <;> simp_all [optionOkOr,XRn_Join_toQ,allRun,fromLimbsClosureCallMut,P,Array.make]

#print axioms checked
end XSa_CheckedQ
