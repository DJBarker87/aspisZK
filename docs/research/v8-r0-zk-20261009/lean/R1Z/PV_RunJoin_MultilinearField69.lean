import R1Z.PV_RunJoin_MaskScalarTotal69
import PV_B3_Install222
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MultilinearField69
open Aeneas Aeneas.Std Result PV_B3_Copy_222
abbrev C := aspis_core.field.CM31
abbrev Q := aspis_core.field.QM31
theorem cadd (self rhs : C) : ∃ c,aspis_core.field.CM31.add self rhs=ok c := by
  obtain ⟨m,h_m⟩ := PV_RunJoin_MaskScalarTotal69.add self.a rhs.a
  obtain ⟨m1,h_m1⟩ := PV_RunJoin_MaskScalarTotal69.add self.b rhs.b
  simp only [aspis_core.field.CM31.add,lift,bind_tc_ok,h_m,h_m1]
  exact ⟨_,rfl⟩


theorem csub (self rhs : C) : ∃ c,aspis_core.field.CM31.sub self rhs=ok c := by
  obtain ⟨m,h_m⟩ := PV_RunJoin_MaskScalarTotal69.sub self.a rhs.a
  obtain ⟨m1,h_m1⟩ := PV_RunJoin_MaskScalarTotal69.sub self.b rhs.b
  simp only [aspis_core.field.CM31.sub,lift,bind_tc_ok,h_m,h_m1]
  exact ⟨_,rfl⟩


theorem cmul (self rhs : C) : ∃ c,aspis_core.field.CM31.mul self rhs=ok c := by
  obtain ⟨m0,h_m0⟩ := PV_RunJoin_MaskScalarTotal69.mul self.a rhs.a
  obtain ⟨m1,h_m1⟩ := PV_RunJoin_MaskScalarTotal69.mul self.b rhs.b
  let i := self.a
  let i1 := (core.convert.num.FromU64U32.from i)
  let i2 := self.b
  let i3 := (core.convert.num.FromU64U32.from i2)
  let i4 := (Std.U64.wrapping_add i1 i3)
  let i5 := rhs.a
  let i6 := (core.convert.num.FromU64U32.from i5)
  let i7 := rhs.b
  let i8 := (core.convert.num.FromU64U32.from i7)
  let i9 := (Std.U64.wrapping_add i6 i8)
  let i10 := (Std.U64.wrapping_mul i4 i9)
  obtain ⟨m2,h_m2⟩ := PV_RunJoin_MaskScalarTotal69.reduce i10
  obtain ⟨m,h_m⟩ := PV_RunJoin_MaskScalarTotal69.sub m0 m1
  obtain ⟨m3,h_m3⟩ := PV_RunJoin_MaskScalarTotal69.sub m2 m0
  obtain ⟨m4,h_m4⟩ := PV_RunJoin_MaskScalarTotal69.sub m3 m1
  simp only [aspis_core.field.CM31.mul,lift,bind_tc_ok,h_m0,h_m1,h_m2,h_m,h_m3,h_m4]
  exact ⟨_,rfl⟩


theorem mulR (x : C) : ∃ c,aspis_core.field.mul_by_r x=ok c := by
  obtain ⟨m,h_m⟩ := PV_RunJoin_MaskScalarTotal69.double x.a
  obtain ⟨m1,h_m1⟩ := PV_RunJoin_MaskScalarTotal69.sub m x.b
  obtain ⟨m2,h_m2⟩ := PV_RunJoin_MaskScalarTotal69.double x.b
  obtain ⟨m3,h_m3⟩ := PV_RunJoin_MaskScalarTotal69.add x.a m2
  simp only [aspis_core.field.mul_by_r,lift,bind_tc_ok,h_m,h_m1,h_m2,h_m3]
  exact ⟨_,rfl⟩


theorem qadd (self rhs : Q) : ∃ c,aspis_core.field.QM31.add self rhs=ok c := by
  obtain ⟨c,h_c⟩ := cadd self.c0 rhs.c0
  obtain ⟨c1,h_c1⟩ := cadd self.c1 rhs.c1
  simp only [aspis_core.field.QM31.add,lift,bind_tc_ok,h_c,h_c1]
  exact ⟨_,rfl⟩


theorem qmul (self rhs : Q) : ∃ c,aspis_core.field.QM31.mul self rhs=ok c := by
  obtain ⟨m0,h_m0⟩ := cmul self.c0 rhs.c0
  obtain ⟨m1,h_m1⟩ := cmul self.c1 rhs.c1
  obtain ⟨c,h_c⟩ := cadd self.c0 self.c1
  obtain ⟨c1,h_c1⟩ := cadd rhs.c0 rhs.c1
  obtain ⟨m2,h_m2⟩ := cmul c c1
  obtain ⟨c2,h_c2⟩ := mulR m1
  obtain ⟨c3,h_c3⟩ := cadd m0 c2
  obtain ⟨c4,h_c4⟩ := csub m2 m0
  obtain ⟨c5,h_c5⟩ := csub c4 m1
  simp only [aspis_core.field.QM31.mul,lift,bind_tc_ok,h_m0,h_m1,h_c,h_c1,h_m2,h_c2,h_c3,h_c4,h_c5]
  exact ⟨_,rfl⟩


theorem qsub (a b : Q) : ∃ c,aspis_core.field.QM31.sub a b=ok c := by
  obtain ⟨c0,h0⟩ := csub a.c0 b.c0
  obtain ⟨c1,h1⟩ := csub a.c1 b.c1
  exact ⟨⟨c0,c1⟩,by simp only [aspis_core.field.QM31.sub,h0,h1,lift,bind_tc_ok]⟩

theorem eq (a b : Q) : ∃ c,aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq a b=ok c := by
  simp only [aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
    aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq,
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,lift,bind_tc_ok]
  repeat' first | (exact ⟨_,rfl⟩) | (simp only [bind_tc_ok]) | split
#print axioms cadd
#print axioms csub
#print axioms cmul
#print axioms mulR
#print axioms qadd
#print axioms qmul
#print axioms qsub
#print axioms eq
end R1Z.PV_RunJoin_MultilinearField69
