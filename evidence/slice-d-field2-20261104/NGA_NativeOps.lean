import NFN_GeometryPart02
import RPv_FJm_QMSquare
import RPt_FIo_MulUValues
import RPt_FIo_WideMulValues
set_option autoImplicit false
noncomputable section
namespace NGA_NativeOps
open Aeneas Aeneas.Std Result
open AspisR1 AspisR1.FIo_FieldBridge
abbrev Canon := FIo_QMValues.Canon
abbrev decode (x : NQ) := AspisR1CurrentWide.Proof.decodeQM (qm x)

theorem cm_square_total (x : NC) : NFN_LPi_Total.Total (FIo_Native.aspis_core.field.CM31.square x) := by
 simp only [FIo_Native.aspis_core.field.CM31.square,lift,bind_tc_ok]
 apply NFN_LPi_Total.bind_total (NFN_LPi_Total.reduce _);intro a
 apply NFN_LPi_Total.bind_total (NFN_LPi_Total.m31_mul _ _);intro b
 change NFN_LPi_Total.Total (do
   let c ← FIo_Native.aspis_core.field.M31.add b b
   ok (⟨a,c⟩ : NC))
 apply NFN_LPi_Total.bind_total (NFN_LPi_Total.m31_add _ _);intro c
 exact ⟨_,rfl⟩

theorem qm_square_total (x : NQ) : NFN_LPi_Total.Total (FIo_Native.aspis_core.field.QM31.square x) := by
 unfold FIo_Native.aspis_core.field.QM31.square
 apply NFN_LPi_Total.bind_total (cm_square_total _);intro a
 apply NFN_LPi_Total.bind_total (cm_square_total _);intro b
 apply NFN_LPi_Total.bind_total (NFN_LPi_Total.by_r _);intro r
 apply NFN_LPi_Total.bind_total (NFN_LPi_Total.cm_add _ _);intro lo
 apply NFN_LPi_Total.bind_total (NFN_LPi_Total.cm_mul _ _);intro ab
 change NFN_LPi_Total.Total (do
   let hi ← FIo_Native.aspis_core.field.CM31.add ab ab
   ok (⟨lo,hi⟩ : NQ))
 apply NFN_LPi_Total.bind_total (NFN_LPi_Total.cm_add _ _);intro hi
 exact ⟨_,rfl⟩

theorem product (x y : NQ) (hx : Canon x) (hy : Canon y) :
 ∃ z, FIo_Native.aspis_core.field.QM31.mul x y=ok z ∧ Canon z ∧ decode z=decode x*decode y := by
 obtain ⟨z,h⟩ := NFN_LPi_Total.qm_mul x y
 exact ⟨z,h,FIo_QMMulValues.mul x y z hx hy h⟩

theorem square (x : NQ) (hx : Canon x) :
 ∃ z, FIo_Native.aspis_core.field.QM31.square x=ok z ∧ Canon z ∧ decode z=decode x*decode x := by
 obtain ⟨z,h⟩ := qm_square_total x
 exact ⟨z,h,FJm_QMSquare.value x z hx h⟩

theorem mul_u (x : NQ) (hx : Canon x) :
 ∃ z, FIo_Native.aspis_core.field.wide_exact.mul_u x=ok z ∧ Canon z ∧
   decode z=AspisWideTower.wideU*decode x := by
 obtain ⟨z,h⟩ := NFN_LPi_Total.mul_u x
 exact ⟨z,h,FIo_MulUValues.value x z hx h⟩

theorem addition (x y : NQ) (hx : Canon x) (hy : Canon y) :
 ∃ z, FIo_Native.aspis_core.field.QM31.add x y=ok z ∧ Canon z ∧ decode z=decode x+decode y := by
 obtain ⟨z,h⟩ := NFN_LPi_Total.qm_add x y
 exact ⟨z,h,FIo_QMValues.add x y z hx hy h⟩

#print axioms cm_square_total
#print axioms qm_square_total
#print axioms product
#print axioms square
#print axioms mul_u
#print axioms addition
end NGA_NativeOps
end
