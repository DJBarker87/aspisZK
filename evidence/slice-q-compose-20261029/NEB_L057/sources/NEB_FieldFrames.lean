import NEB_CMCalls
import NEB_QMCalls
import NEB_WideCalls
import NEB_ByRCalls
import NEB_PureFrame
set_option autoImplicit false
namespace NEB_FieldFrames
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

/-- Existing translated field bridge, with exact value and empty pure frame. -/
theorem cm_mul {S Event : Type} (state : S) (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.mul x y=ok z ∧ canonC z ∧
      cw z=mulC (cw x) (cw y) ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.CM31.mul x y)=ok (z,state,[]) := by
  obtain ⟨z,run,canonical,value⟩ := LPi_FieldValues.cm_mul x y hx hy
  exact ⟨z,run,canonical,value,NEB_PureFrame.successful state _ _ run⟩

/-- Existing translated field bridge, with exact value and empty pure frame. -/
theorem qm_mul {S Event : Type} (state : S) (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.mul x y=ok z ∧ canonQ z ∧
      qw z=mulQ (qw x) (qw y) ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.QM31.mul x y)=ok (z,state,[]) := by
  obtain ⟨z,run,canonical,value⟩ := LPi_TowerValues.qm_mul x y hx hy
  exact ⟨z,run,canonical,value,NEB_PureFrame.successful state _ _ run⟩

/-- Existing translated field bridge, with exact value and empty pure frame. -/
theorem wide_mul {S Event : Type} (state : S) (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y=ok z ∧ canonE z ∧
      ew z=mulE (ew x) (ew y) ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y)=ok (z,state,[]) := by
  obtain ⟨z,run,canonical,value⟩ := LPi_TowerValues.wide_mul x y hx hy
  exact ⟨z,run,canonical,value,NEB_PureFrame.successful state _ _ run⟩

/-- Existing translated field bridge, with exact value and empty pure frame. -/
theorem by_r {S Event : Type} (state : S) (x : NC) (hx : canonC x) :
    ∃ z, FIo_Native.aspis_core.field.mul_by_r x=ok z ∧ canonC z ∧
      cw z=byR (cw x) ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.mul_by_r x)=ok (z,state,[]) := by
  obtain ⟨z,run,canonical,value⟩ := LPi_FieldValues.by_r x hx
  exact ⟨z,run,canonical,value,NEB_PureFrame.successful state _ _ run⟩

/-- Existing translated field bridge, with exact value and empty pure frame. -/
theorem mul_u {S Event : Type} (state : S) (x : NQ) (hx : canonQ x) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.mul_u x=ok z ∧ canonQ z ∧
      qw z=mulU (qw x) ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.wide_exact.mul_u x)=ok (z,state,[]) := by
  obtain ⟨z,run,canonical,value⟩ := LPi_TowerValues.mul_u x hx
  exact ⟨z,run,canonical,value,NEB_PureFrame.successful state _ _ run⟩

/-- Existing translated field bridge, with exact value and empty pure frame. -/
theorem cm_scale {S Event : Type} (state : S) (x : NC) (scalar : U32) :
    ∃ z, FIo_Native.aspis_core.field.CM31.mul_m31 x scalar=ok z ∧ canonC z ∧
      cw z=((x.a.val*scalar.val)%2147483647,(x.b.val*scalar.val)%2147483647) ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.CM31.mul_m31 x scalar)=ok (z,state,[]) := by
  obtain ⟨z,run,canonical,value⟩ := LPi_MixedValues.cm_m31 x scalar
  exact ⟨z,run,canonical,value,NEB_PureFrame.successful state _ _ run⟩

/-- Existing translated field bridge, with exact value and empty pure frame. -/
theorem qm_scale {S Event : Type} (state : S) (x : NQ) (scalar : U32) :
    ∃ z, FIo_Native.aspis_core.field.QM31.mul_m31 x scalar=ok z ∧ canonQ z ∧
      qw z=(((x.c0.a.val*scalar.val)%2147483647,(x.c0.b.val*scalar.val)%2147483647),((x.c1.a.val*scalar.val)%2147483647,(x.c1.b.val*scalar.val)%2147483647)) ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.QM31.mul_m31 x scalar)=ok (z,state,[]) := by
  obtain ⟨z,run,canonical,value⟩ := LPi_MixedValues.qm_m31 x scalar
  exact ⟨z,run,canonical,value,NEB_PureFrame.successful state _ _ run⟩

/-- Existing translated field bridge, with exact value and empty pure frame. -/
theorem wide_scale {S Event : Type} (state : S) (x : NE) (scalar : U32) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 x scalar=ok z ∧ canonE z ∧
      ew z=(NBG_FieldDischarge.scaleQ (qw x.c0) (scalar.val%2147483647),NBG_FieldDischarge.scaleQ (qw x.c1) (scalar.val%2147483647)) ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 x scalar)=ok (z,state,[]) := by
  obtain ⟨z,run,canonical,value⟩ := NBG_FieldDischarge.wide_scale x scalar
  exact ⟨z,run,canonical,value,NEB_PureFrame.successful state _ _ run⟩

/-- Existing translated field bridge, with exact value and empty pure frame. -/
theorem wide_mixed {S Event : Type} (state : S) (x : NE) (y : NQ) (hx : canonE x) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 x y=ok z ∧ canonE z ∧
      ew z=(mulQ (qw x.c0) (NBG_FieldDischarge.modQ (qw y)),mulQ (qw x.c1) (NBG_FieldDischarge.modQ (qw y))) ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 x y)=ok (z,state,[]) := by
  obtain ⟨z,run,canonical,value⟩ := NBG_FieldDischarge.wide_qm x y hx
  exact ⟨z,run,canonical,value,NEB_PureFrame.successful state _ _ run⟩
#print axioms cm_mul
#print axioms qm_mul
#print axioms wide_mul
#print axioms by_r
#print axioms mul_u
#print axioms cm_scale
#print axioms qm_scale
#print axioms wide_scale
#print axioms wide_mixed
end NEB_FieldFrames
