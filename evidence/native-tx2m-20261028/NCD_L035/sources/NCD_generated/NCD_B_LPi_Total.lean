-- Inherited body, import-only deployed-cohort retarget.
import NCD_B_LPf_BaseMultiply
import RPz7_FIo_NativeFuns
set_option autoImplicit false
namespace AspisR1.LPi_Total
open Aeneas Aeneas.Std Result
abbrev NC := FIo_Native.aspis_core.field.CM31
abbrev NQ := FIo_Native.aspis_core.field.QM31
abbrev NE := FIo_Native.aspis_core.field.wide_exact.WideExact

def Total {α : Type} (r : Result α) : Prop := ∃ z, r = ok z

theorem bind_total {α β : Type} {r : Result α} {k : α → Result β}
    (hr : Total r) (hk : ∀ x, Total (k x)) : Total (r >>= k) := by
  obtain ⟨x,hx⟩ := hr
  rw [hx,bind_tc_ok]
  exact hk x

theorem m31_mul (x y : U32) : Total (FIo_Native.aspis_core.field.M31.mul x y) := by
  obtain ⟨z,h,_,_⟩ := LPf_BaseMultiply.source x y
  exact ⟨z,h⟩

theorem reduce (x : U64) : Total (FIo_Native.aspis_core.field.M31.reduce_u64 x) := by
  obtain ⟨z,h,_,_⟩ := LPf_CoreReduction.source x
  exact ⟨z,by simp only [FIo_Native.aspis_core.field.M31.reduce_u64,h,bind_tc_ok]⟩

theorem m31_add (x y : U32) : Total (FIo_Native.aspis_core.field.M31.add x y) := by
  simp only [FIo_Native.aspis_core.field.M31.add,lift,bind_tc_ok]
  split <;> exact ⟨_,rfl⟩

theorem m31_sub (x y : U32) : Total (FIo_Native.aspis_core.field.M31.sub x y) := by
  simp only [FIo_Native.aspis_core.field.M31.sub,lift,bind_tc_ok]
  split <;> exact ⟨_,rfl⟩

theorem cm_add (x y : NC) : Total (FIo_Native.aspis_core.field.CM31.add x y) := by
  unfold FIo_Native.aspis_core.field.CM31.add
  apply bind_total (m31_add _ _); intro a
  apply bind_total (m31_add _ _); intro b
  exact ⟨_,rfl⟩

theorem cm_sub (x y : NC) : Total (FIo_Native.aspis_core.field.CM31.sub x y) := by
  unfold FIo_Native.aspis_core.field.CM31.sub
  apply bind_total (m31_sub _ _); intro a
  apply bind_total (m31_sub _ _); intro b
  exact ⟨_,rfl⟩

theorem cm_mul (x y : NC) : Total (FIo_Native.aspis_core.field.CM31.mul x y) := by
  unfold FIo_Native.aspis_core.field.CM31.mul
  apply bind_total (m31_mul _ _); intro a
  apply bind_total (m31_mul _ _); intro b
  simp only [lift,bind_tc_ok]
  apply bind_total (reduce _); intro c
  apply bind_total (m31_sub _ _); intro d
  apply bind_total (m31_sub _ _); intro e
  apply bind_total (m31_sub _ _); intro f
  exact ⟨_,rfl⟩

theorem by_r (x : NC) : Total (FIo_Native.aspis_core.field.mul_by_r x) := by
  unfold FIo_Native.aspis_core.field.mul_by_r FIo_Native.aspis_core.field.M31.double
  apply bind_total (m31_add _ _); intro a
  apply bind_total (m31_sub _ _); intro b
  apply bind_total (m31_add _ _); intro c
  apply bind_total (m31_add _ _); intro d
  exact ⟨_,rfl⟩

theorem qm_add (x y : NQ) : Total (FIo_Native.aspis_core.field.QM31.add x y) := by
  unfold FIo_Native.aspis_core.field.QM31.add
  apply bind_total (cm_add _ _); intro a
  apply bind_total (cm_add _ _); intro b
  exact ⟨_,rfl⟩

theorem qm_sub (x y : NQ) : Total (FIo_Native.aspis_core.field.QM31.sub x y) := by
  unfold FIo_Native.aspis_core.field.QM31.sub
  apply bind_total (cm_sub _ _); intro a
  apply bind_total (cm_sub _ _); intro b
  exact ⟨_,rfl⟩

theorem qm_mul (x y : NQ) : Total (FIo_Native.aspis_core.field.QM31.mul x y) := by
  unfold FIo_Native.aspis_core.field.QM31.mul
  apply bind_total (cm_mul _ _); intro a
  apply bind_total (cm_mul _ _); intro b
  apply bind_total (cm_add _ _); intro c
  apply bind_total (cm_add _ _); intro d
  apply bind_total (cm_mul _ _); intro e
  apply bind_total (by_r _); intro f
  apply bind_total (cm_add _ _); intro g
  apply bind_total (cm_sub _ _); intro h
  apply bind_total (cm_sub _ _); intro i
  exact ⟨_,rfl⟩

theorem mul_u (x : NQ) : Total (FIo_Native.aspis_core.field.wide_exact.mul_u x) := by
  unfold FIo_Native.aspis_core.field.wide_exact.mul_u
  apply bind_total (by_r _); intro a
  exact ⟨_,rfl⟩

theorem wide_mul (x y : NE) : Total (FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y) := by
  unfold FIo_Native.aspis_core.field.wide_exact.WideExact.mul
  apply bind_total (qm_mul _ _); intro a
  apply bind_total (qm_mul _ _); intro b
  apply bind_total (qm_add _ _); intro c
  apply bind_total (qm_add _ _); intro d
  apply bind_total (qm_mul _ _); intro e
  apply bind_total (mul_u _); intro f
  apply bind_total (qm_add _ _); intro g
  apply bind_total (qm_sub _ _); intro h
  apply bind_total (qm_sub _ _); intro i
  exact ⟨_,rfl⟩

#print axioms bind_total
#print axioms m31_mul
#print axioms reduce
#print axioms m31_add
#print axioms m31_sub
#print axioms cm_add
#print axioms cm_sub
#print axioms cm_mul
#print axioms by_r
#print axioms qm_add
#print axioms qm_sub
#print axioms qm_mul
#print axioms mul_u
#print axioms wide_mul
end AspisR1.LPi_Total
