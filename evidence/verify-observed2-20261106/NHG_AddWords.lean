import NHG_FinishLeaves
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NHG_AddWords
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
abbrev Q := AspisR1SemanticCallExtraction.aspis_core.field.QM31
abbrev Canonical := NHG_FinishLeaves.Canonical
abbrev Words := AspisR1.ExtractedMaskTowerAdd.wordsQM

theorem cases_mod (p a b : Nat) (positive : 0<p) (ha : a<p) (hb : b<p) :
 (if p≤a+b then a+b-p else a+b)=(a+b)%p := by
 by_cases large : p≤a+b
 · rw [if_pos large,Nat.mod_eq_sub_mod large,Nat.mod_eq_of_lt (by omega)]
 · rw [if_neg large,Nat.mod_eq_of_lt (by omega)]

/-- Exact generated add coordinates match the native one-step conditional
sum under the canonical invariant. The existing probe equality is reused. -/
theorem generated (x y : Q) (hx : Canonical x) (hy : Canonical y) :
 ∃ z,AspisR1SemanticCallExtraction.aspis_core.field.QM31.add x y=ok z ∧
 Canonical z ∧ Words (genQToProbe z)=
 ((((genQToProbe x).c0.a.val+(genQToProbe y).c0.a.val)%2147483647,
   ((genQToProbe x).c0.b.val+(genQToProbe y).c0.b.val)%2147483647),
  (((genQToProbe x).c1.a.val+(genQToProbe y).c1.a.val)%2147483647,
   ((genQToProbe x).c1.b.val+(genQToProbe y).c1.b.val)%2147483647)) := by
 obtain ⟨z,call,canonical,natural⟩:=AspisR1.ExtractedMaskTowerAdd.current_qm_add_mod
  (genQToProbe x) (genQToProbe y) hx hy
 have mapped : resultMap genQToProbe
  (AspisR1SemanticCallExtraction.aspis_core.field.QM31.add x y)=ok z := by
  rw [generated_qm_add_eq_probe]
  exact call
 obtain ⟨w,run,identity⟩:=AspisR1PublicPreparation.RawExtractedSemanticCallOpsV23.resultMap_eq_ok_inv genQToProbe _ z mapped
 refine ⟨w,run,?_,?_⟩
 · change AspisR1.ExtractedMaskTowerAdd.CanonicalQM (genQToProbe w)
   rw [identity];exact canonical
 · rw [identity];exact natural

abbrev NQ := FIq_Native.field.QM31
abbrev toProbe := AspisR1.FIv_NativeArithmetic.qm
abbrev NCanonical (x : NQ) := AspisR1.ExtractedMaskTowerAdd.CanonicalQM (toProbe x)

theorem nq_add (x y : NQ) (hx : NCanonical x) (hy : NCanonical y) :
 ∃ z,FIq_Native.field.QM31.add x y=ok z ∧ NCanonical z ∧
 Words (toProbe z)=
 ((((toProbe x).c0.a.val+(toProbe y).c0.a.val)%2147483647,
   ((toProbe x).c0.b.val+(toProbe y).c0.b.val)%2147483647),
  (((toProbe x).c1.a.val+(toProbe y).c1.a.val)%2147483647,
   ((toProbe x).c1.b.val+(toProbe y).c1.b.val)%2147483647)) := by
 obtain ⟨z,call,canonical,natural⟩:=AspisR1.ExtractedMaskTowerAdd.current_qm_add_mod (toProbe x) (toProbe y) hx hy
 have mapped : resultMap toProbe (FIq_Native.field.QM31.add x y)=ok z := by
  change AspisR1.FIv_Map.map toProbe (FIq_Native.field.QM31.add x y)=ok z
  rw [AspisR1.FIv_NativeQM.add]
  exact call
 obtain ⟨w,run,identity⟩:=AspisR1PublicPreparation.RawExtractedSemanticCallOpsV23.resultMap_eq_ok_inv toProbe _ z mapped
 refine ⟨w,run,?_,?_⟩
 · change AspisR1.ExtractedMaskTowerAdd.CanonicalQM (toProbe w)
   rw [identity];exact canonical
 · rw [identity];exact natural

theorem nq_mul (x y : NQ) (hx : NCanonical x) (hy : NCanonical y) :
 ∃ z,FIq_Native.field.QM31.mul x y=ok z ∧ NCanonical z ∧
 NHG_Product.Words (toProbe z)=NHG_Product.NaturalProduct
  (NHG_Product.Words (toProbe x)) (NHG_Product.Words (toProbe y)) := by
 obtain ⟨z,call,canonical,natural⟩:=AspisR1.ExtractedMaskQM31Mul.current_qm_mul_words (toProbe x) (toProbe y) hx hy
 have mapped : resultMap toProbe (FIq_Native.field.QM31.mul x y)=ok z := by
  change AspisR1.FIv_Map.map toProbe (FIq_Native.field.QM31.mul x y)=ok z
  rw [AspisR1.FIv_NativeQM.mul]
  exact call
 obtain ⟨w,run,identity⟩:=AspisR1PublicPreparation.RawExtractedSemanticCallOpsV23.resultMap_eq_ok_inv toProbe _ z mapped
 refine ⟨w,run,?_,?_⟩
 · change AspisR1.ExtractedMaskTowerAdd.CanonicalQM (toProbe w)
   rw [identity];exact canonical
 · rw [identity];exact natural

#print axioms nq_add
#print axioms nq_mul
#print axioms cases_mod
#print axioms generated
end AspisR1.NHG_AddWords
