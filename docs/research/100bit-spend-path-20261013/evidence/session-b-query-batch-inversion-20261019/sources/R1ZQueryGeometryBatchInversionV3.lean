import AspisFormal.CircleGroupOrder
import R1ZQueryGeometryValuesV6
import R1ZBatchInverseAlgebraV5
import R1ZBatchInverseSourceModelV4

set_option autoImplicit false

namespace R1ZQueryGeometryBatchInversionV1

open AspisCircleGroupOrder
open R1ZQueryGeometryValuesV1
open R1ZBatchInverseAlgebraV3
open R1ZBatchInverseSourceModelV1

/-- If every input is nonzero, each prefix product used by the source backward
pass is nonzero. -/
theorem take_prod_ne_zero_of_entries (xs : List (ZMod P))
    (hxs : ∀ i (hi : i < xs.length), xs[i]'hi ≠ 0) :
    ∀ m, m ≤ xs.length → (xs.take m).prod ≠ 0 := by
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
    have hlt : m < xs.length := by omega
    have hpre := ih (by omega)
    have hx := hxs m hlt
    rw [list_take_succ_prod xs m hlt]
    exact mul_ne_zero hpre hx

/-- The complete prefix-product/backward pass on a source-shaped list returns
all pointwise inverses, provided the source zero test accepted every value. -/
theorem source_batch_inverse_model (xs : List (ZMod P))
    (hxs : ∀ i (hi : i < xs.length), xs[i]'hi ≠ 0) :
    backwardsStored xs (prefixRun xs 1) xs.length (xs.prod⁻¹) =
      xs.map Inv.inv := by
  have hnz := take_prod_ne_zero_of_entries xs hxs
  have hp : ∀ i, i < xs.length →
      (prefixRun xs 1).getD i 1 = (xs.take i).prod := by
    intro i hi
    exact prefixRun_getD_eq_take_prod xs i hi
  simpa using backwardsStored_correct xs (prefixRun xs 1) xs.length
    (le_rfl) (fun m hm => hnz m hm) hp xs.prod⁻¹ (by simp)

/-- Five ordered denominators used for one query. This is the mathematical
chunk corresponding to `values=[point.x,point.y,line_x,line_y,line_z]`. -/
def oneQueryValues (px py : ZMod P) (v : Fin 65536) : List (ZMod P) :=
  List.ofFn (queryGeometryValues px py v)

theorem oneQueryValues_length (px py : ZMod P) (v : Fin 65536) :
    (oneQueryValues px py v).length = 5 := by
  simp [oneQueryValues]

theorem oneQueryValues_get (px py : ZMod P) (v : Fin 65536) (i : Fin 5) :
    (oneQueryValues px py v)[i.val]'(by simpa [oneQueryValues] using i.isLt) = queryGeometryValues px py v i := by
  have h := List.getElem_ofFn (f := queryGeometryValues px py v)
    (i := i.val) (by simp)
  simpa [oneQueryValues] using h

/-- For a nonzero five-value query chunk, the source-shaped prefix/backward
model outputs the inverse chunk in the original five-slot order. -/
theorem oneQuery_batch_inverse (px py : ZMod P) (v : Fin 65536)
    (hnz : ∀ i : Fin 5, queryGeometryValues px py v i ≠ 0) :
    backwardsStored (oneQueryValues px py v)
      (prefixRun (oneQueryValues px py v) 1) 5
      ((oneQueryValues px py v).prod⁻¹) =
      (oneQueryValues px py v).map Inv.inv := by
  apply source_batch_inverse_model
  intro i hi
  have hi5 : i < 5 := by simpa [oneQueryValues_length] using hi
  let j : Fin 5 := ⟨i, hi5⟩
  have hget := oneQueryValues_get px py v j
  simpa [j, hget] using hnz j

#print axioms source_batch_inverse_model
#print axioms oneQuery_batch_inverse

end R1ZQueryGeometryBatchInversionV1
