import R1Z.PV_RDB2E_ShaSchedule
namespace R1Z.PV_RDB2E_ShaScalar
set_option autoImplicit false
structure Banks where
  w0 : V
  w1 : V
  w2 : V
  w3 : V
  w4 : V

def window0 (b : Banks) : Window := ⟨b.w0,b.w1,b.w2,b.w3⟩
def window1 (b : Banks) : Window := ⟨b.w1,b.w2,b.w3,b.w4⟩
def window2 (b : Banks) : Window := ⟨b.w2,b.w3,b.w4,b.w0⟩
def window3 (b : Banks) : Window := ⟨b.w3,b.w4,b.w0,b.w1⟩
def window4 (b : Banks) : Window := ⟨b.w4,b.w0,b.w1,b.w2⟩
def bank0 (b : Banks) : Banks := {b with w4:=schedule b.w0 b.w1 b.w2 b.w3}
def bank1 (b : Banks) : Banks := {b with w0:=schedule b.w1 b.w2 b.w3 b.w4}
def bank2 (b : Banks) : Banks := {b with w1:=schedule b.w2 b.w3 b.w4 b.w0}
def bank3 (b : Banks) : Banks := {b with w2:=schedule b.w3 b.w4 b.w0 b.w1}
def bank4 (b : Banks) : Banks := {b with w3:=schedule b.w4 b.w0 b.w1 b.w2}

theorem phase0 (b : Banks) : window1 (bank0 b)=advance (window0 b) := rfl
theorem phase1 (b : Banks) : window2 (bank1 b)=advance (window1 b) := rfl
theorem phase2 (b : Banks) : window3 (bank2 b)=advance (window2 b) := rfl
theorem phase3 (b : Banks) : window4 (bank3 b)=advance (window3 b) := rfl
theorem phase4 (b : Banks) : window0 (bank4 b)=advance (window4 b) := rfl

#print axioms phase0
#print axioms phase1
#print axioms phase2
#print axioms phase3
#print axioms phase4
end R1Z.PV_RDB2E_ShaScalar
