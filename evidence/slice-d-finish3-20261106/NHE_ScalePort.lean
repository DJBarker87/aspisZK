import NHE_WidePort
import NGM_RoundScale
set_option autoImplicit false
namespace NHE_ScalePort
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem cm (x : NC) (s : U32) :
 (do let z ← FIo_Native.aspis_core.field.CM31.mul_m31 x s;ok (FIo_FieldBridge.cm z))=
 AspisR1CurrentWide.field.CM31.mul_m31 (FIo_FieldBridge.cm x) s := by
 simp only [FIo_Native.aspis_core.field.CM31.mul_m31,AspisR1CurrentWide.field.CM31.mul_m31,FIo_FieldBridge.cm]
 simp only [←FIo_M31MulBridge.same,bind_assoc_eq,bind_tc_ok]

theorem qm (x : NQ) (s : U32) :
 (do let z ← FIo_Native.aspis_core.field.QM31.mul_m31 x s;ok (FIo_FieldBridge.qm z))=
 AspisR1CurrentWide.field.QM31.mul_m31 (FIo_FieldBridge.qm x) s := by
 simp only [FIo_Native.aspis_core.field.QM31.mul_m31,AspisR1CurrentWide.field.QM31.mul_m31,FIo_FieldBridge.qm]
 simp only [←cm,bind_assoc_eq,bind_tc_ok]

theorem wide (x : NE) (s : U32) :
 (do let z ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 x s;ok (FIo_FieldBridge.wide z))=
 AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31 (FIo_FieldBridge.wide x) s := by
 simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31,AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31,FIo_FieldBridge.wide,FIo_Native.aspis_core.field.P,AspisR1CurrentWide.field.P]
 simp only [←qm,bind_assoc_eq,bind_tc_ok]

theorem quarter (x : NE) :
 FIo_FieldBridge.map FIo_Install.fromE (FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 x 536870912#u32)=
 SAG_StageScale.mulM (FIo_Install.fromE x) 536870912#u32 := by
 obtain ⟨z,run,_,_⟩ := NGM_RoundScale.total x
 have same := wide x 536870912#u32
 rw [run] at same
 simp only [bind_tc_ok] at same
 rw [run]
 change ok (FIo_Install.fromE z)=SAG_StageScale.mulM (FIo_Install.fromE x) 536870912#u32
 unfold SAG_StageScale.mulM
 change ok (FIo_Install.fromE z)=(do let z ← AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31 (FIo_FieldBridge.wide x) 536870912#u32;ok (SAQ_WideABI.fromW z))
 rw [←same]
 rfl

#print axioms cm
#print axioms qm
#print axioms wide
#print axioms quarter
end NHE_ScalePort
