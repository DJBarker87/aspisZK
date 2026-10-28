import FIo_NativeFuns
import AspisR1CurrentWide.Types
set_option autoImplicit false
namespace NBG_GetterPorts
abbrev NE := FIo_Native.aspis_core.field.wide_exact.WideExact
abbrev NQ := FIo_Native.aspis_core.field.QM31

def qm (x : NQ) : AspisR1CurrentWide.field.QM31 :=
  ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def wide (x : NE) : AspisR1CurrentWide.field.wide_exact.WideExact :=
  ⟨qm x.c0,qm x.c1⟩

theorem c0 (x : NE) : (wide x).c0 = qm x.c0 := rfl
theorem c1 (x : NE) : (wide x).c1 = qm x.c1 := rfl

#print axioms c0
#print axioms c1
end NBG_GetterPorts
