import RPu_FIv_Arithmetic
import RPu_FIq_Native08
import ExtractedMaskScalarExact
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_ScalarArithmetic
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic
open FIv_NativeValue (K Canon decode)
open FIv_Map (map map_bind map_ok)

abbrev P := ExtractedMaskTowerAdd.P

theorem scalar_nat (s : U32) : ExtractedMaskScalarExact.scalarEmbedding s=(s.val : K) := by
  ext <;> simp only [ExtractedMaskScalarExact.scalarEmbedding,AspisV8R15.ExactTowerBase.QM31Exact,
    AspisV8R15.ExactTowerBase.CM31Exact,QuadraticAlgebra.re_natCast,
    QuadraticAlgebra.im_natCast,QuadraticAlgebra.re_zero,QuadraticAlgebra.im_zero]

theorem cm_mapped (x : NC) (s : U32) :
    map cm (field.CM31.mul_m31 x s)=AspisR1SelectedMaskProbe.field.CM31.mul_m31 (cm x) s := by
  simp only [field.CM31.mul_m31,AspisR1SelectedMaskProbe.field.CM31.mul_m31,cm,
    map_bind,map_ok,m31_mul]
theorem qm_mapped (x : NQ) (s : U32) :
    map qm (field.QM31.mul_m31 x s)=AspisR1SelectedMaskProbe.field.QM31.mul_m31 (qm x) s := by
  simp only [field.QM31.mul_m31,AspisR1SelectedMaskProbe.field.QM31.mul_m31,qm,
    ← cm_mapped,bind_map,map_bind,map_ok]
theorem mul (x out : NQ) (s : U32) (run : field.QM31.mul_m31 x s=ok out) :
    Canon out ∧ decode out=decode x*(s.val : K) := by
  obtain ⟨z,hz,hc,hv⟩ := ExtractedMaskScalarExact.current_qm_mul_m31_exact (qm x) s
  have same := qm_mapped x s
  rw [run,map_ok,hz] at same
  have eq := Result.ok.inj same
  rw [← eq] at hc hv
  exact ⟨hc,hv.trans (by rw [scalar_nat])⟩

def lifted (s : U32) : NQ := ⟨⟨s,0#u32⟩,⟨0#u32,0#u32⟩⟩
theorem lift_run (s : U32) :
    pool_v1.pair_forest_semantic_terminal.lift_m31 s=ok (lifted s) := by
  simp only [pool_v1.pair_forest_semantic_terminal.lift_m31,field.CM31.from_m31,
    field.QM31.from_cm31,field.CM31.ZERO,field.M31.ZERO,bind_tc_ok,lifted]
theorem lift_value (s : U32) (hs : s.val<P) :
    Canon (lifted s) ∧ decode (lifted s)=(s.val : K) := by
  constructor
  · change (s.val<P ∧ (0#u32).val<P) ∧ ((0#u32).val<P ∧ (0#u32).val<P)
    exact ⟨⟨hs,by decide⟩,⟨by decide,by decide⟩⟩
  · exact scalar_nat s
#print axioms scalar_nat
#print axioms cm_mapped
#print axioms qm_mapped
#print axioms mul
#print axioms lift_run
#print axioms lift_value
end AspisR1.FIw_ScalarArithmetic
end
