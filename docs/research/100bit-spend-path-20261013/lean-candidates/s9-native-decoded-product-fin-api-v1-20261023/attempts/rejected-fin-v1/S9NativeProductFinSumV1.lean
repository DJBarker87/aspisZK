import S9NativeDecodedScalarProductV1
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open scoped BigOperators
namespace AspisR1S9NativeProductFinSumV1
open AspisR1S9NativeInputProductWitnessV1
open AspisR1S9NativeDecodedScalarProductV1

def term (p : NativePair) : AspisWideTower.WideExact :=
  decodeNative p.1 * scalarEmbed p.2

/-- Existing product sum, now exposed as ordinary multiplication of the
actual native decoded operands. Only carrier interpretation changes. -/
theorem nativeProductSum_eq_map_sum (ps : List NativePair) :
    nativeProductSum ps=(ps.map term).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change AspisR1FastDotsTailFieldProductRootV1.scalarProduct (sourcePair p) +
      nativeProductSum ps = term p + (ps.map term).sum
    rw [native_scalar_product_eq_decoded_mul_embed,ih]

/-- Same Mathlib ofFn/getElem route as the retained GREEN
FinishDotIndexedSourceSumV1.productSum_eq_indexed_sum. No failed generic
list/Fin candidate or new finite-sum algebra is used. -/
theorem nativeProductSum_eq_fin_sum (ps : List NativePair) :
    nativeProductSum ps=∑ i : Fin ps.length, term (ps.get i) := by
  rw [nativeProductSum_eq_map_sum,←List.ofFn_getElem_eq_map ps term,List.sum_ofFn]
  rfl

/-- Preserve the actual source list and its derived length while exposing
exact Fin16/Fin4 types required by the source contraction. -/
theorem nativeProductSum_eq_fin_sum_cast (ps : List NativePair) (n : Nat)
    (hlen : ps.length=n) :
    nativeProductSum ps=∑ i : Fin n, term (ps.get (Fin.cast hlen.symm i)) := by
  subst n
  simpa only [Fin.cast_refl] using nativeProductSum_eq_fin_sum ps

#print axioms nativeProductSum_eq_map_sum
#print axioms nativeProductSum_eq_fin_sum
#print axioms nativeProductSum_eq_fin_sum_cast
end AspisR1S9NativeProductFinSumV1
