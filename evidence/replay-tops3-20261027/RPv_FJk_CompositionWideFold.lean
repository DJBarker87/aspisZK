import RPv_FJk_PolynomialHorner
import RPv_FIv_CompositionValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_CompositionWideFold
open Aeneas Aeneas.Std
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K decode)
open FIw_ArrayValue (decoded)
variable {L : Type} [Field L]
theorem low {N : Usize} (f : K →+* L) (theta : K) (a : Array NQ N) :
    f (FIv_HornerAlgebra.low theta a.val)=
    TerminalHornerCore.sourceMixHorner (f theta) (List.ofFn (fun i=>f (decoded a i))) := by
  rw [FJk_NativePolynomial.value,FJk_ArrayList.value,FJk_PolynomialMap.map,
    List.map_ofFn,FJk_PolynomialHorner.value]
  rfl
/-- Transport the COMPLETE two-fold composition, preserving all source coefficients. -/
theorem value (f : K →+* L) (theta : K) (semantic : Array NQ 24#usize)
    (poseidon : Array NQ 4#usize) (seed : NQ) :
    f (FIv_CompositionValue.polynomial theta semantic poseidon seed)=
    ExtractedMaskTerminalHorner.composeGroups (f theta) (f (decode seed))
      (fun i=>f (decoded semantic i)) (fun i=>f (decoded poseidon i)) := by
  unfold FIv_CompositionValue.polynomial
  rw [map_add,map_add,map_mul,map_mul,map_pow,map_pow,low,low]
  unfold ExtractedMaskTerminalHorner.composeGroups
  rw [ExtractedMaskTerminalHorner.seededHorner_eq_source,
    ExtractedMaskTerminalHorner.seededHorner_eq_source,List.length_ofFn,List.length_ofFn]
  ring_nf
  congr 2
#print axioms low
#print axioms value
end AspisR1.FJk_CompositionWideFold
end
