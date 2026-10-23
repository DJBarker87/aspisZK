import S9SharedContiguousContractionV1
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace AspisR1S9TensorDigitsContractionV1
open AspisR1S9SharedContiguousContractionV1
/-- The actual contiguous16-by4 split has the existing three radix-four
factor coordinates. Generic ring homomorphisms keep field decoders opaque. -/
theorem tensor_weight_digits {R S : Type*} [CommSemiring R] [CommSemiring S]
    (embed : R →+* S) (p2 p3 p4 : Nat → R) (i : Fin 64) :
    tensorWeight
      (fun j : Fin 16 => embed (p2 (j.val%4)*p3 (j.val/4)))
      (fun s : Fin 4 => embed (p4 s.val)) i =
      embed (p2 (i.val%4)*p3 ((i.val/4)%4)*p4 ((i.val/16)%4)) := by
  let ij : Fin 4 × Fin 16 := finProdFinEquiv.symm i
  have he : sourceIndex ij.1 ij.2=i :=
    (finProdFinEquiv (m:=4) (n:=16)).apply_symm_apply i
  have hv : i.val=ij.2.val+16*ij.1.val := by
    have h := congrArg Fin.val he
    simpa only [sourceIndex_val] using h.symm
  have h4 := ij.1.isLt
  have h16 := ij.2.isLt
  have e2 : i.val%4=ij.2.val%4 := by omega
  have e3 : (i.val/4)%4=ij.2.val/4 := by omega
  have e4 : (i.val/16)%4=ij.1.val := by omega
  change embed (p2 (ij.2.val%4)*p3 (ij.2.val/4))*embed (p4 ij.1.val)=_
  rw [←map_mul,e2,e3,e4]
#print axioms tensor_weight_digits
end AspisR1S9TensorDigitsContractionV1
