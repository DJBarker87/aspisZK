import R1Z.PV_RDB2E_ShaScalar
namespace R1Z.PV_RDB2E_ShaScalar
set_option autoImplicit false
structure Window where
  v0 : V
  v1 : V
  v2 : V
  v3 : V

def advance (w : Window) : Window := ⟨w.v1,w.v2,w.v3,schedule w.v0 w.v1 w.v2 w.v3⟩
def fromWords (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : W) : Window :=
  ⟨⟨a3,a2,a1,a0⟩,⟨a7,a6,a5,a4⟩,⟨a11,a10,a9,a8⟩,⟨a15,a14,a13,a12⟩⟩
/-- Four scalar schedule recurrence steps, in source wrapping-add order. -/
def extendWords (a0 a1 a2 a3 a4 a9 a10 a11 a12 a14 a15 : W) : V :=
  let w16:=((a0+sigma0 a1)+a9)+sigma1 a14
  let w17:=((a1+sigma0 a2)+a10)+sigma1 a15
  let w18:=((a2+sigma0 a3)+a11)+sigma1 w16
  let w19:=((a3+sigma0 a4)+a12)+sigma1 w17
  ⟨w19,w18,w17,w16⟩

theorem schedule_scalar (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : W) :
    (advance (fromWords a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)).v3=
      extendWords a0 a1 a2 a3 a4 a9 a10 a11 a12 a14 a15 := rfl

theorem retained_window (w : Window) :
    (advance w).v0=w.v1 ∧ (advance w).v1=w.v2 ∧ (advance w).v2=w.v3 := ⟨rfl,rfl,rfl⟩

#print axioms schedule_scalar
#print axioms retained_window
end R1Z.PV_RDB2E_ShaScalar
