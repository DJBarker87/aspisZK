-- PCUH item 4: the constants' OWN transparent fresh definitions (PCQF_E007, aspis_core field emission, extended Aeneas b59d5188,
-- overflow checks ON, frozen 4bb3b3f) are compared with the gate constants that earlier phases used as the instantiation of the
-- opaque cross-crate externals (PRVD_ConstBind shims `X : Result T := ok <gate X>`).
import Aeneas
import RPu_FIq_Native10
import NFN_ExtractedGeometry
open Aeneas Aeneas.Std Result ControlFlow Error

namespace PRVFresh_const_E007

/-- [aspis_core::field::M31] -/
@[reducible] def field.M31 := Std.U32
/-- [aspis_core::field::CM31] -/
structure field.CM31 where
  a : field.M31
  b : field.M31
/-- [aspis_core::field::QM31] -/
structure field.QM31 where
  c0 : field.CM31
  c1 : field.CM31

/-- [aspis_core::field::{aspis_core::field::M31}::ZERO]  (PCQF_E007 Funs.lean line 46) -/
@[irreducible] def field.M31.ZERO : field.M31 := 0#u32
/-- [aspis_core::field::{aspis_core::field::M31}::ONE]  (PCQF_E007 Funs.lean line 51) -/
@[irreducible] def field.M31.ONE : field.M31 := 1#u32
/-- [aspis_core::field::{aspis_core::field::QM31}::ZERO]  (PCQF_E007 Funs.lean line 417) -/
@[irreducible] def field.QM31.ZERO : field.QM31 :=
  { c0 := { a := 0#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }
/-- [aspis_core::field::{aspis_core::field::QM31}::ONE]  (PCQF_E007 Funs.lean line 424) -/
@[irreducible] def field.QM31.ONE : field.QM31 :=
  { c0 := { a := 1#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

end PRVFresh_const_E007

namespace PRVEq.const

theorem M31_ZERO : (PRVFresh_const_E007.field.M31.ZERO : Std.U32) = (NEW_GeometryActual.aspis_core.field.M31.ZERO : Std.U32) := by
  unfold PRVFresh_const_E007.field.M31.ZERO NEW_GeometryActual.aspis_core.field.M31.ZERO; rfl
theorem M31_ONE : (PRVFresh_const_E007.field.M31.ONE : Std.U32) = (NEW_GeometryActual.aspis_core.field.M31.ONE : Std.U32) := by
  unfold PRVFresh_const_E007.field.M31.ONE NEW_GeometryActual.aspis_core.field.M31.ONE; rfl

theorem M31_ONE_FIq : (PRVFresh_const_E007.field.M31.ONE : Std.U32) = (FIq_Native.field.M31.ONE : Std.U32) := by
  unfold PRVFresh_const_E007.field.M31.ONE FIq_Native.field.M31.ONE; rfl
theorem M31_ZERO_FIq : (PRVFresh_const_E007.field.M31.ZERO : Std.U32) = (FIq_Native.field.M31.ZERO : Std.U32) := by
  unfold PRVFresh_const_E007.field.M31.ZERO FIq_Native.field.M31.ZERO; rfl

/-- limbwise (the fresh and gate QM31 are distinct structure types) -/
theorem QM31_ZERO :
    (PRVFresh_const_E007.field.QM31.ZERO.c0.a : Std.U32) = (FIq_Native.field.QM31.ZERO.c0.a : Std.U32) ∧
    (PRVFresh_const_E007.field.QM31.ZERO.c0.b : Std.U32) = (FIq_Native.field.QM31.ZERO.c0.b : Std.U32) ∧
    (PRVFresh_const_E007.field.QM31.ZERO.c1.a : Std.U32) = (FIq_Native.field.QM31.ZERO.c1.a : Std.U32) ∧
    (PRVFresh_const_E007.field.QM31.ZERO.c1.b : Std.U32) = (FIq_Native.field.QM31.ZERO.c1.b : Std.U32) := by
  unfold PRVFresh_const_E007.field.QM31.ZERO FIq_Native.field.QM31.ZERO
  exact ⟨rfl, rfl, rfl, rfl⟩
theorem QM31_ONE :
    (PRVFresh_const_E007.field.QM31.ONE.c0.a : Std.U32) = (FIq_Native.field.QM31.ONE.c0.a : Std.U32) ∧
    (PRVFresh_const_E007.field.QM31.ONE.c0.b : Std.U32) = (FIq_Native.field.QM31.ONE.c0.b : Std.U32) ∧
    (PRVFresh_const_E007.field.QM31.ONE.c1.a : Std.U32) = (FIq_Native.field.QM31.ONE.c1.a : Std.U32) ∧
    (PRVFresh_const_E007.field.QM31.ONE.c1.b : Std.U32) = (FIq_Native.field.QM31.ONE.c1.b : Std.U32) := by
  unfold PRVFresh_const_E007.field.QM31.ONE FIq_Native.field.QM31.ONE
  exact ⟨rfl, rfl, rfl, rfl⟩

end PRVEq.const
#print axioms PRVEq.const.M31_ZERO
#print axioms PRVEq.const.M31_ONE
#print axioms PRVEq.const.QM31_ZERO
#print axioms PRVEq.const.QM31_ONE
#print axioms PRVEq.const.M31_ONE_FIq
#print axioms PRVEq.const.M31_ZERO_FIq
