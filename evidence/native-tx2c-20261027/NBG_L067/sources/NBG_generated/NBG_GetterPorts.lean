import FIo_FieldBridge
set_option autoImplicit false
namespace NBG_GetterPorts
open AspisR1 FIo_FieldBridge

theorem c0 (x : NE) : (wide x).c0 = qm x.c0 := rfl
theorem c1 (x : NE) : (wide x).c1 = qm x.c1 := rfl

#print axioms c0
#print axioms c1
end NBG_GetterPorts
