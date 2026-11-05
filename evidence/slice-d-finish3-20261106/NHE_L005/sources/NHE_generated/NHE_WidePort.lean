import NHE_QMPort
set_option autoImplicit false
namespace NHE_WidePort
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem mul_u (x : NQ) (hx : canonQ x) :
 (do let z ← FIo_Native.aspis_core.field.wide_exact.mul_u x;ok (FIo_FieldBridge.qm z))=
 AspisR1CurrentWide.field.wide_exact.mul_u (FIo_FieldBridge.qm x) := by
 simp only [FIo_Native.aspis_core.field.wide_exact.mul_u,AspisR1CurrentWide.field.wide_exact.mul_u,FIo_FieldBridge.qm]
 simp only [←NHE_QMPort.by_r x.c1 hx.2,bind_assoc_eq,bind_tc_ok]

theorem mul (x y : NE) (hx : canonE x) (hy : canonE y) :
 (do let z ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y;ok (FIo_FieldBridge.wide z))=
 AspisR1CurrentWide.field.wide_exact.WideExact.mul (FIo_FieldBridge.wide x) (FIo_FieldBridge.wide y) := by
 obtain ⟨ac,hac,cac,_⟩ := LPi_TowerValues.qm_mul x.c0 y.c0 hx.1 hy.1
 have sac := NHE_QMPort.mul x.c0 y.c0 hx.1 hy.1
 rw [hac] at sac
 simp only [bind_tc_ok] at sac
 obtain ⟨bd,hbd,cbd,_⟩ := LPi_TowerValues.qm_mul x.c1 y.c1 hx.2 hy.2
 have sbd := NHE_QMPort.mul x.c1 y.c1 hx.2 hy.2
 rw [hbd] at sbd
 simp only [bind_tc_ok] at sbd
 obtain ⟨a,ha,ca,_⟩ := LPi_TowerValues.qm_add x.c0 x.c1 hx.1 hx.2
 have sa := NGW_CurrentAddPort.qm x.c0 x.c1 hx.1 hx.2
 rw [ha] at sa
 simp only [bind_tc_ok] at sa
 obtain ⟨b,hb,cb,_⟩ := LPi_TowerValues.qm_add y.c0 y.c1 hy.1 hy.2
 have sb := NGW_CurrentAddPort.qm y.c0 y.c1 hy.1 hy.2
 rw [hb] at sb
 simp only [bind_tc_ok] at sb
 obtain ⟨cross,hcross,ccross,_⟩ := LPi_TowerValues.qm_mul a b ca cb
 have scross := NHE_QMPort.mul a b ca cb
 rw [hcross] at scross
 simp only [bind_tc_ok] at scross
 obtain ⟨r,hr,cr,_⟩ := LPi_TowerValues.mul_u bd cbd
 have sr := mul_u bd cbd
 rw [hr] at sr
 simp only [bind_tc_ok] at sr
 obtain ⟨lo,hlo,clo,_⟩ := LPi_TowerValues.qm_add ac r cac cr
 have slo := NGW_CurrentAddPort.qm ac r cac cr
 rw [hlo] at slo
 simp only [bind_tc_ok] at slo
 obtain ⟨diff,hdiff,cdiff,_⟩ := LPi_TowerValues.qm_sub cross ac ccross cac
 have sdiff := NHE_QMPort.sub cross ac ccross cac
 rw [hdiff] at sdiff
 simp only [bind_tc_ok] at sdiff
 obtain ⟨hi,hhi,chi,_⟩ := LPi_TowerValues.qm_sub diff bd cdiff cbd
 have shi := NHE_QMPort.sub diff bd cdiff cbd
 rw [hhi] at shi
 simp only [bind_tc_ok] at shi
 simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.mul,AspisR1CurrentWide.field.wide_exact.WideExact.mul,FIo_FieldBridge.wide,hac,←sac,hbd,←sbd,ha,←sa,hb,←sb,hcross,←scross,hr,←sr,hlo,←slo,hdiff,←sdiff,hhi,←shi,bind_tc_ok]

theorem adopted (x y : NE) (hx : canonE x) (hy : canonE y) :
 FIo_FieldBridge.map FIo_Install.fromE (FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y)=
 FIn_Polynomial.mul (FIo_Install.fromE x) (FIo_Install.fromE y) := by
 obtain ⟨z,run,_,_⟩ := LPi_TowerValues.wide_mul x y hx hy
 have same := mul x y hx hy
 rw [run] at same
 simp only [bind_tc_ok] at same
 rw [run]
 change ok (FIo_Install.fromE z) = FIn_Polynomial.mul (FIo_Install.fromE x) (FIo_Install.fromE y)
 unfold FIn_Polynomial.mul
 change ok (FIo_Install.fromE z) =
   (do let out ← AspisR1CurrentWide.field.wide_exact.WideExact.mul (FIo_FieldBridge.wide x) (FIo_FieldBridge.wide y)
       ok (SAQ_WideABI.fromW out))
 rw [←same]
 rfl
#print axioms mul_u
#print axioms mul
#print axioms adopted
end NHE_WidePort
