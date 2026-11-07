import NMT_Transport_T10
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMT_Transport
open Aeneas Aeneas.Std
def toT11 : NMT_tx1.transport.Variant → AspisR1CurrentCaller.transport.Variant
 | .S1 => .S1
 | .S2 => .S2
 | .D => .D
def fromT11 : AspisR1CurrentCaller.transport.Variant → NMT_tx1.transport.Variant
 | .S1 => .S1
 | .S2 => .S2
 | .D => .D
@[simp] theorem toT11_inverse (x : NMT_tx1.transport.Variant) : fromT11 (toT11 x)=x := by
 cases x <;> simp [toT11,fromT11]
#print axioms toT11_inverse
@[simp] theorem fromT11_inverse (x : AspisR1CurrentCaller.transport.Variant) : toT11 (fromT11 x)=x := by
 cases x <;> simp [fromT11,toT11]
#print axioms fromT11_inverse
end AspisR1.NMT_Transport
