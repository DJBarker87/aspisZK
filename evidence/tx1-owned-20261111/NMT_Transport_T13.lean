import NMT_Transport_T12
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMT_Transport
open Aeneas Aeneas.Std
def toT13 (x : NMT_tx1.verifier.BatchedWeights) : AspisR1CurrentCaller.verifier.BatchedWeights :=
 ⟨x.«raw»,x.terms⟩
def fromT13 (x : AspisR1CurrentCaller.verifier.BatchedWeights) : NMT_tx1.verifier.BatchedWeights :=
 ⟨x.«raw»,x.terms⟩
@[simp] theorem toT13_inverse (x : NMT_tx1.verifier.BatchedWeights) : fromT13 (toT13 x)=x := by
 cases x <;> simp [toT13,fromT13]
#print axioms toT13_inverse
@[simp] theorem fromT13_inverse (x : AspisR1CurrentCaller.verifier.BatchedWeights) : toT13 (fromT13 x)=x := by
 cases x <;> simp [fromT13,toT13]
#print axioms fromT13_inverse
end AspisR1.NMT_Transport
