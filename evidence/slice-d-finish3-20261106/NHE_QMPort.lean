import NHE_CMPort
set_option autoImplicit false
namespace NHE_QMPort
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem by_r (x : NC) (hx : canonC x) :
 (do let z ← FIo_Native.aspis_core.field.mul_by_r x;ok (FIo_FieldBridge.cm z))=
 AspisR1CurrentWide.field.mul_by_r (FIo_FieldBridge.cm x) := by
 obtain ⟨a,ha,_,ca⟩ := LPi_NatBase.add x.a x.a hx.1 hx.1
 obtain ⟨b,hb,_,_⟩ := LPi_NatBase.sub a x.b ca hx.2
 obtain ⟨c,hc,_,cc⟩ := LPi_NatBase.add x.b x.b hx.2 hx.2
 obtain ⟨d,hd,_,_⟩ := LPi_NatBase.add x.a c hx.1 cc
 have ha' := (FIo_M31Bridge.add x.a x.a hx.1 hx.1).symm.trans ha
 have hb' := (FIo_M31SubBridge.sub a x.b ca hx.2).symm.trans hb
 have hc' := (FIo_M31Bridge.add x.b x.b hx.2 hx.2).symm.trans hc
 have hd' := (FIo_M31Bridge.add x.a c hx.1 cc).symm.trans hd
 simp only [FIo_Native.aspis_core.field.mul_by_r,AspisR1CurrentWide.field.mul_by_r,FIo_Native.aspis_core.field.M31.double,AspisR1CurrentWide.field.M31.double,FIo_FieldBridge.cm,ha,hb,hc,hd,ha',hb',hc',hd',bind_tc_ok]

theorem sub (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
 (do let z ← FIo_Native.aspis_core.field.QM31.sub x y;ok (FIo_FieldBridge.qm z))=
 AspisR1CurrentWide.field.QM31.sub (FIo_FieldBridge.qm x) (FIo_FieldBridge.qm y) := by
 simp only [FIo_Native.aspis_core.field.QM31.sub,AspisR1CurrentWide.field.QM31.sub,FIo_FieldBridge.qm]
 simp only [←NHE_CMPort.sub x.c0 y.c0 hx.1 hy.1,←NHE_CMPort.sub x.c1 y.c1 hx.2 hy.2,bind_assoc_eq,bind_tc_ok]

theorem mul (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
 (do let z ← FIo_Native.aspis_core.field.QM31.mul x y;ok (FIo_FieldBridge.qm z))=
 AspisR1CurrentWide.field.QM31.mul (FIo_FieldBridge.qm x) (FIo_FieldBridge.qm y) := by
 obtain ⟨ac,hac,cac,_⟩ := LPi_FieldValues.cm_mul x.c0 y.c0 hx.1 hy.1
 have sac := NHE_CMPort.mul x.c0 y.c0 hx.1 hy.1
 rw [hac] at sac
 simp only [bind_tc_ok] at sac
 obtain ⟨bd,hbd,cbd,_⟩ := LPi_FieldValues.cm_mul x.c1 y.c1 hx.2 hy.2
 have sbd := NHE_CMPort.mul x.c1 y.c1 hx.2 hy.2
 rw [hbd] at sbd
 simp only [bind_tc_ok] at sbd
 obtain ⟨a,ha,ca,_⟩ := LPi_FieldValues.cm_add x.c0 x.c1 hx.1 hx.2
 have sa := NGW_CurrentAddPort.cm x.c0 x.c1 hx.1 hx.2
 rw [ha] at sa
 simp only [bind_tc_ok] at sa
 obtain ⟨b,hb,cb,_⟩ := LPi_FieldValues.cm_add y.c0 y.c1 hy.1 hy.2
 have sb := NGW_CurrentAddPort.cm y.c0 y.c1 hy.1 hy.2
 rw [hb] at sb
 simp only [bind_tc_ok] at sb
 obtain ⟨cross,hcross,ccross,_⟩ := LPi_FieldValues.cm_mul a b ca cb
 have scross := NHE_CMPort.mul a b ca cb
 rw [hcross] at scross
 simp only [bind_tc_ok] at scross
 obtain ⟨r,hr,cr,_⟩ := LPi_FieldValues.by_r bd cbd
 have sr := by_r bd cbd
 rw [hr] at sr
 simp only [bind_tc_ok] at sr
 obtain ⟨lo,hlo,clo,_⟩ := LPi_FieldValues.cm_add ac r cac cr
 have slo := NGW_CurrentAddPort.cm ac r cac cr
 rw [hlo] at slo
 simp only [bind_tc_ok] at slo
 obtain ⟨diff,hdiff,cdiff,_⟩ := LPi_FieldValues.cm_sub cross ac ccross cac
 have sdiff := NHE_CMPort.sub cross ac ccross cac
 rw [hdiff] at sdiff
 simp only [bind_tc_ok] at sdiff
 obtain ⟨hi,hhi,chi,_⟩ := LPi_FieldValues.cm_sub diff bd cdiff cbd
 have shi := NHE_CMPort.sub diff bd cdiff cbd
 rw [hhi] at shi
 simp only [bind_tc_ok] at shi
 simp only [FIo_Native.aspis_core.field.QM31.mul,AspisR1CurrentWide.field.QM31.mul,FIo_FieldBridge.qm,hac,←sac,hbd,←sbd,ha,←sa,hb,←sb,hcross,←scross,hr,←sr,hlo,←slo,hdiff,←sdiff,hhi,←shi,bind_tc_ok]

#print axioms by_r
#print axioms sub
#print axioms mul
end NHE_QMPort
