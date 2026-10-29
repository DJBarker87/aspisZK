import AspisR72Sampler.Types
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Carrier52
abbrev CM := U32 × U32
abbrev Q := CM × CM
abbrev Point := Q × Q
abbrev OC := AspisR72Sampler.field.CM31
abbrev OQ := AspisR72Sampler.field.QM31
abbrev OP := AspisR72Sampler.circle.SecureCirclePoint
def encCM (a : CM) : OC := ⟨a.1,a.2⟩
def decCM (a : OC) : CM := (a.a,a.b)
def encQ (a : Q) : OQ := ⟨encCM a.1,encCM a.2⟩
def decQ (a : OQ) : Q := (decCM a.c0,decCM a.c1)
def encPoint (a : Point) : OP := ⟨encQ a.1,encQ a.2⟩
def decPoint (a : OP) : Point := (decQ a.x,decQ a.y)
def encError (e : Bool) : AspisR72Sampler.circle.CirclePointError :=
  if e then .ParameterInCm31Subfield else .SingularParameter
def encOutcome (r : core.result.Result Point Bool) :
    core.result.Result OP AspisR72Sampler.circle.CirclePointError :=
  match r with | .Ok p => .Ok (encPoint p) | .Err e => .Err (encError e)
theorem cm_roundtrip (a : CM) : decCM (encCM a)=a := rfl
theorem q_roundtrip (a : Q) : decQ (encQ a)=a := rfl
theorem point_roundtrip (a : Point) : decPoint (encPoint a)=a := rfl
theorem cm_source (a : OC) : encCM (decCM a)=a := rfl
theorem q_source (a : OQ) : encQ (decQ a)=a := rfl
theorem point_source (a : OP) : encPoint (decPoint a)=a := rfl
theorem cm_a (a : CM) : (encCM a).a=a.1 := rfl
theorem cm_b (a : CM) : (encCM a).b=a.2 := rfl
theorem q_c0 (a : Q) : (encQ a).c0=encCM a.1 := rfl
theorem q_c1 (a : Q) : (encQ a).c1=encCM a.2 := rfl

#print axioms encCM
#print axioms decCM
#print axioms encQ
#print axioms decQ
#print axioms encPoint
#print axioms decPoint
#print axioms encError
#print axioms encOutcome
#print axioms cm_roundtrip
#print axioms q_roundtrip
#print axioms point_roundtrip
#print axioms cm_source
#print axioms q_source
#print axioms point_source
#print axioms cm_a
#print axioms cm_b
#print axioms q_c0
#print axioms q_c1
end R1Z.PV_RunJoin_CircleR72Carrier52
