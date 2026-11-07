import NMT_Transport_T2
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMT_Transport
open Aeneas Aeneas.Std
def toT3 (x : NMT_tx1.aspis_core.field.wide_exact.WideExact) : AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact :=
 ⟨toT1 (x.c0),toT1 (x.c1)⟩
def fromT3 (x : AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact) : NMT_tx1.aspis_core.field.wide_exact.WideExact :=
 ⟨fromT1 (x.c0),fromT1 (x.c1)⟩
@[simp] theorem toT3_inverse (x : NMT_tx1.aspis_core.field.wide_exact.WideExact) : fromT3 (toT3 x)=x := by
 cases x <;> simp [toT3,fromT3]
#print axioms toT3_inverse
@[simp] theorem fromT3_inverse (x : AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact) : toT3 (fromT3 x)=x := by
 cases x <;> simp [fromT3,toT3]
#print axioms fromT3_inverse
end AspisR1.NMT_Transport
