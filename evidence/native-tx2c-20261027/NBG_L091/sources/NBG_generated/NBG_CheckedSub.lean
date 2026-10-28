import FIo_NativeFuns
import AspisR1CurrentWide.Funs
import FIo_ScalarBridge
import NBG_GetterPorts
import LPi_TowerValues
set_option autoImplicit false
noncomputable section
namespace NBG_CheckedSub
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
theorem m31 (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    FIo_Native.aspis_core.field.M31.sub x y=AspisR1CurrentWide.field.M31.sub x y := by
  have hadd : x+(2147483647#u32)=ok (U32.wrapping_add x (2147483647#u32)) :=
    FIo_ScalarBridge.add x (2147483647#u32) (by scalar_tac)
  have val : (U32.wrapping_add x (2147483647#u32)).val=x.val+2147483647 := by
    rw [U32.wrapping_add_val_eq,Nat.mod_eq_of_lt (by scalar_tac)]
    rfl
  have hsub : (U32.wrapping_add x (2147483647#u32))-y=
      ok (U32.wrapping_sub (U32.wrapping_add x (2147483647#u32)) y) :=
    FIo_ScalarBridge.sub _ y (by rw [val]; omega)
  simp only [FIo_Native.aspis_core.field.M31.sub,AspisR1CurrentWide.field.M31.sub,
    FIo_Native.aspis_core.field.P,AspisR1CurrentWide.field.P,hadd,hsub,lift,bind_tc_ok]
  split
  · rename_i h
    have last := FIo_ScalarBridge.sub
      (U32.wrapping_sub (U32.wrapping_add x (2147483647#u32)) y) (2147483647#u32) (by scalar_tac)
    rw [last]
    rfl
  · rfl


def cm (x : NC) : AspisR1CurrentWide.field.CM31 := ⟨x.a,x.b⟩

theorem cm_result (x y : NC) (hx : canonC x) (hy : canonC y) : ∃ z,
    AspisR1CurrentWide.field.CM31.sub (cm x) (cm y) = ok (cm z) ∧
      canonC z ∧ cw z = subC (cw x) (cw y) := by
  obtain ⟨a,ha,va,ca⟩ := LPi_NatBase.sub x.a y.a hx.1 hy.1
  obtain ⟨b,hb,vb,cb⟩ := LPi_NatBase.sub x.b y.b hx.2 hy.2
  have ar := (m31 x.a y.a hx.1 hy.1).symm.trans ha
  have br := (m31 x.b y.b hx.2 hy.2).symm.trans hb
  exact ⟨⟨a,b⟩,by simp only [AspisR1CurrentWide.field.CM31.sub,cm,ar,br,bind_tc_ok],
    ⟨ca,cb⟩,Prod.ext va vb⟩

theorem qm_result (x y : NQ) (hx : canonQ x) (hy : canonQ y) : ∃ z,
    AspisR1CurrentWide.field.QM31.sub (NBG_GetterPorts.qm x) (NBG_GetterPorts.qm y) =
      ok (NBG_GetterPorts.qm z) ∧ canonQ z ∧ qw z = subQ (qw x) (qw y) := by
  obtain ⟨a,ha,ca,va⟩ := cm_result x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,vb⟩ := cm_result x.c1 y.c1 hx.2 hy.2
  simp only [cm] at ha hb
  exact ⟨⟨a,b⟩,by simp only [AspisR1CurrentWide.field.QM31.sub,NBG_GetterPorts.qm,ha,hb,bind_tc_ok],
    ⟨ca,cb⟩,Prod.ext va vb⟩

theorem wide_result (x y : NE) (hx : canonE x) (hy : canonE y) : ∃ z,
    AspisR1CurrentWide.field.wide_exact.WideExact.sub (NBG_GetterPorts.wide x)
      (NBG_GetterPorts.wide y) = ok (NBG_GetterPorts.wide z) ∧ canonE z ∧
      ew z = (subQ (qw x.c0) (qw y.c0),subQ (qw x.c1) (qw y.c1)) := by
  obtain ⟨a,ha,ca,va⟩ := qm_result x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,vb⟩ := qm_result x.c1 y.c1 hx.2 hy.2
  exact ⟨⟨a,b⟩,by simp only [AspisR1CurrentWide.field.wide_exact.WideExact.sub,
    NBG_GetterPorts.wide,ha,hb,bind_tc_ok],⟨ca,cb⟩,Prod.ext va vb⟩

#print axioms m31
#print axioms cm_result
#print axioms qm_result
#print axioms wide_result
end NBG_CheckedSub
