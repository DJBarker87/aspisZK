import NMT_TransportBase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMT_Transport
open Aeneas Aeneas.Std
def toT0 (x : NMT_tx1.aspis_core.field.CM31) : AspisR1CurrentCaller.aspis_core.field.CM31 :=
 ⟨x.a,x.b⟩
def fromT0 (x : AspisR1CurrentCaller.aspis_core.field.CM31) : NMT_tx1.aspis_core.field.CM31 :=
 ⟨x.a,x.b⟩
@[simp] theorem toT0_inverse (x : NMT_tx1.aspis_core.field.CM31) : fromT0 (toT0 x)=x := by
 cases x <;> simp [toT0,fromT0]
#print axioms toT0_inverse
@[simp] theorem fromT0_inverse (x : AspisR1CurrentCaller.aspis_core.field.CM31) : toT0 (fromT0 x)=x := by
 cases x <;> simp [fromT0,toT0]
#print axioms fromT0_inverse
end AspisR1.NMT_Transport
