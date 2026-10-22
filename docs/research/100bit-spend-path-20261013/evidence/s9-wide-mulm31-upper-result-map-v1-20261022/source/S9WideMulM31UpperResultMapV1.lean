import S9WideMulM31FullResultMapV1
import AspisR1S9WideMulM31CutV1.Funs
import CurrentWideBaseBridge

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideMulM31UpperResultMapV1
open AspisR1S9WideMulM31FullResultMapV1

/-- Move a current-side bind whose input is the mapped result back to the
source-side input, retaining the full Result behavior. -/
theorem bind_mapR {A B C : Type} (f : A → B) (r : Result A)
    (k : B → Result C) :
    Bind.bind (mapR f r) k = Bind.bind r (fun x => k (f x)) := by
  cases r <;> rfl

theorem qm_mul_m31_result_map
    (x : AspisR1S9WideMulM31CutV1.field.QM31)
    (s : AspisR1S9WideMulM31CutV1.field.M31) :
    mapR mapQM (AspisR1S9WideMulM31CutV1.field.QM31.mul_m31 x s) =
      AspisR1CurrentWide.field.QM31.mul_m31 (mapQM x) (mapM31 s) := by
  unfold AspisR1S9WideMulM31CutV1.field.QM31.mul_m31
    AspisR1CurrentWide.field.QM31.mul_m31
  simp only [mapQM]
  rw [← cm_mul_m31_result_map x.c0 s, ← cm_mul_m31_result_map x.c1 s]
  simp only [mapR_bind, bind_mapR, mapQM, mapCM, mapM31] <;> rfl

theorem current_qm_mul_m31_eq_map
    (q : AspisR1S9WideMulM31CutV1.field.QM31)
    (i : AspisR1S9WideMulM31CutV1.field.M31) :
    AspisR1CurrentWide.field.QM31.mul_m31 (mapQM q) i =
      mapR mapQM (AspisR1S9WideMulM31CutV1.field.QM31.mul_m31 q i) := by
  simpa only [mapM31] using (qm_mul_m31_result_map q i).symm

theorem wide_mul_m31_result_map
    (x : AspisR1S9WideMulM31CutV1.field.wide_exact.WideExact)
    (s : AspisR1S9WideMulM31CutV1.field.M31) :
    mapR mapWide (AspisR1S9WideMulM31CutV1.field.wide_exact.WideExact.mul_m31 x s) =
      AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31 (mapWide x) (mapM31 s) := by
  unfold AspisR1S9WideMulM31CutV1.field.wide_exact.WideExact.mul_m31
    AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31
    AspisR1S9WideMulM31CutV1.field.P AspisR1CurrentWide.field.P
  simp only [mapWide, mapM31]
  simp only [current_qm_mul_m31_eq_map]
  simp only [mapR_bind, bind_mapR, mapWide, mapQM, mapCM, mapM31] <;> rfl

#print axioms bind_mapR
#print axioms qm_mul_m31_result_map
#print axioms current_qm_mul_m31_eq_map
#print axioms wide_mul_m31_result_map

end AspisR1S9WideMulM31UpperResultMapV1
