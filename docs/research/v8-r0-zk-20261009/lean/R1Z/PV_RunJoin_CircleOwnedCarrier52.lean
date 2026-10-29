import R1Z.PV_AL_CircleOwnedTypes
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleOwnedCarrier52
abbrev CM := U32 × U32
abbrev Q := CM × CM
abbrev Point := Q × Q
abbrev OC := PV_AL_CircleOwned.aspis_core.field.CM31
abbrev OQ := PV_AL_CircleOwned.aspis_core.field.QM31
abbrev OP := PV_AL_CircleOwned.aspis_core.circle.SecureCirclePoint
def encCM (a : CM) : OC := ⟨a.1,a.2⟩
def decCM (a : OC) : CM := (a.a,a.b)
def encQ (a : Q) : OQ := ⟨encCM a.1,encCM a.2⟩
def decQ (a : OQ) : Q := (decCM a.c0,decCM a.c1)
def encPoint (a : Point) : OP := ⟨encQ a.1,encQ a.2⟩
def decPoint (a : OP) : Point := (decQ a.x,decQ a.y)
theorem cm_roundtrip (a : CM) : decCM (encCM a)=a := rfl
theorem q_roundtrip (a : Q) : decQ (encQ a)=a := rfl
theorem point_roundtrip (a : Point) : decPoint (encPoint a)=a := rfl
theorem cm_source (a : OC) : encCM (decCM a)=a := rfl
theorem q_source (a : OQ) : encQ (decQ a)=a := rfl
theorem point_source (a : OP) : encPoint (decPoint a)=a := rfl

#print axioms encCM
#print axioms decCM
#print axioms encQ
#print axioms decQ
#print axioms encPoint
#print axioms decPoint
#print axioms cm_roundtrip
#print axioms q_roundtrip
#print axioms point_roundtrip
#print axioms cm_source
#print axioms q_source
#print axioms point_source
end R1Z.PV_RunJoin_CircleOwnedCarrier52
