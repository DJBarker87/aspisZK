import S9TensorDigitsContractionV1
set_option autoImplicit false
open scoped BigOperators
namespace AspisR1S9TensorModelTransportV1
open AspisR1S9SharedContiguousContractionV1
open AspisR1S9TensorDigitsContractionV1

theorem tensor_weight_congr {E : Type*} [Mul E]
    (low low' : Fin 16 → E) (high high' : Fin 4 → E)
    (hl : ∀ j,low j=low' j) (hh : ∀ s,high s=high' s) (i : Fin 64) :
    tensorWeight low high i=tensorWeight low' high' i := by
  let ij : Fin 4 × Fin 16 := finProdFinEquiv.symm i
  change low ij.2*high ij.1=low' ij.2*high' ij.1
  exact congrArg₂ (fun x y : E => x*y) (hl ij.2) (hh ij.1)

/-- Symbolic transport of source-derived low/high meanings. Concrete field
readers/decoders never enter normalization of the64-term sum. -/
theorem transport_model_sum {R S : Type*} [CommSemiring R] [CommSemiring S]
    (embed : R →+* S) (p2 p3 p4 : Nat → R) (f : Fin 64 → S)
    (low : Fin 16 → S) (high : Fin 4 → S) (value : S)
    (hl : ∀ j,low j=embed (p2 (j.val%4)*p3 (j.val/4)))
    (hh : ∀ s,high s=embed (p4 s.val))
    (hv : value=∑ i : Fin 64,f i*tensorWeight low high i) :
    value=∑ i : Fin 64,f i*embed (p2 (i.val%4)*p3 ((i.val/4)%4)*p4 ((i.val/16)%4)) := by
  apply hv.trans
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun x : S => f i*x)
  exact (tensor_weight_congr low
    (fun j => embed (p2 (j.val%4)*p3 (j.val/4))) high
    (fun s => embed (p4 s.val)) hl hh i).trans (tensor_weight_digits embed p2 p3 p4 i)
#print axioms tensor_weight_congr
#print axioms transport_model_sum
end AspisR1S9TensorModelTransportV1
