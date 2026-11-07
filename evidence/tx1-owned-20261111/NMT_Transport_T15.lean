import NMT_Transport_T14
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMT_Transport
open Aeneas Aeneas.Std
def toT15 (x : NMT_tx1.verifier.Accumulator) : AspisR1CurrentCaller.verifier.Accumulator :=
 ⟨vec (fun z => toT1 (z)) (x.weights),toT3 (x.rhs),toT1 (x.power),x.next⟩
def fromT15 (x : AspisR1CurrentCaller.verifier.Accumulator) : NMT_tx1.verifier.Accumulator :=
 ⟨vec (fun z => fromT1 (z)) (x.weights),fromT3 (x.rhs),fromT1 (x.power),x.next⟩
@[simp] theorem toT15_inverse (x : NMT_tx1.verifier.Accumulator) : fromT15 (toT15 x)=x := by
 cases x <;> simp [toT15,fromT15]
#print axioms toT15_inverse
@[simp] theorem fromT15_inverse (x : AspisR1CurrentCaller.verifier.Accumulator) : toT15 (fromT15 x)=x := by
 cases x <;> simp [fromT15,toT15]
#print axioms fromT15_inverse
end AspisR1.NMT_Transport
