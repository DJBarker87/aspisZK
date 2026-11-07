import NMT_Transport_T13
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMT_Transport
open Aeneas Aeneas.Std
def toT14 (x : NMT_tx1.verifier.QueryGeometry) : AspisR1CurrentCaller.verifier.QueryGeometry :=
 ⟨x.start,x.inverses,x.line_z⟩
def fromT14 (x : AspisR1CurrentCaller.verifier.QueryGeometry) : NMT_tx1.verifier.QueryGeometry :=
 ⟨x.start,x.inverses,x.line_z⟩
@[simp] theorem toT14_inverse (x : NMT_tx1.verifier.QueryGeometry) : fromT14 (toT14 x)=x := by
 cases x <;> simp [toT14,fromT14]
#print axioms toT14_inverse
@[simp] theorem fromT14_inverse (x : AspisR1CurrentCaller.verifier.QueryGeometry) : toT14 (fromT14 x)=x := by
 cases x <;> simp [fromT14,toT14]
#print axioms fromT14_inverse
end AspisR1.NMT_Transport
