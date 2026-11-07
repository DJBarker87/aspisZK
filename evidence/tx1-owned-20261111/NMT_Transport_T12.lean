import NMT_Transport_T11
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMT_Transport
open Aeneas Aeneas.Std
def toT12 (x : NMT_tx1.verifier.Prepared) : AspisR1CurrentCaller.verifier.Prepared :=
 ⟨toT11 (x.variant),x.roots,toT3 (x.gamma),toT3 (x.kappa),arr (fun z => toT3 (z)) (x.alpha),toT1 (x.rho),x.queries,arr (fun z => toT1 (z)) (x.semantic_alpha),arr (fun z => toT2 (z)) (x.z),toT3 (x.claim),x.state⟩
def fromT12 (x : AspisR1CurrentCaller.verifier.Prepared) : NMT_tx1.verifier.Prepared :=
 ⟨fromT11 (x.variant),x.roots,fromT3 (x.gamma),fromT3 (x.kappa),arr (fun z => fromT3 (z)) (x.alpha),fromT1 (x.rho),x.queries,arr (fun z => fromT1 (z)) (x.semantic_alpha),arr (fun z => fromT2 (z)) (x.z),fromT3 (x.claim),x.state⟩
@[simp] theorem toT12_inverse (x : NMT_tx1.verifier.Prepared) : fromT12 (toT12 x)=x := by
 cases x <;> simp [toT12,fromT12]
#print axioms toT12_inverse
@[simp] theorem fromT12_inverse (x : AspisR1CurrentCaller.verifier.Prepared) : toT12 (fromT12 x)=x := by
 cases x <;> simp [fromT12,toT12]
#print axioms fromT12_inverse
end AspisR1.NMT_Transport
