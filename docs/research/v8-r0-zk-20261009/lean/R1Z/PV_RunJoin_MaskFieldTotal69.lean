import R1Z.PV_RunJoin_MaskScalarTotal69
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MaskFieldTotal69
open Aeneas Aeneas.Std Result PV_B3_Copy_117
abbrev C := aspis_core.field.CM31
abbrev Q := aspis_core.field.QM31

theorem cnew (a b : U32) : ∃ c,aspis_core.field.CM31.new a b=ok c := ⟨_,rfl⟩

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

theorem csquare (self : C) : ∃ c,aspis_core.field.CM31.square self=ok c := by
  let i := self.a
  let i1 := (core.convert.num.FromU64U32.from i)
  let i2 := self.b
  let i3 := (core.convert.num.FromU64U32.from i2)
  let i4 := (Std.U64.wrapping_add i1 i3)
  let i5 := (core.convert.num.FromU64U32.from i)
  let i6 := (core.convert.num.FromU64U32.from aspis_core.field.P)
  let i7 := (Std.U64.wrapping_add i5 i6)
  let i8 := (core.convert.num.FromU64U32.from i2)
  let i9 := (Std.U64.wrapping_sub i7 i8)
  let i10 := (Std.U64.wrapping_mul i4 i9)
  obtain ⟨m,h_m⟩ := PV_RunJoin_MaskScalarTotal69.reduce i10
  obtain ⟨m1,h_m1⟩ := PV_RunJoin_MaskScalarTotal69.mul self.a self.b
  obtain ⟨m2,h_m2⟩ := PV_RunJoin_MaskScalarTotal69.double m1
  simp only [aspis_core.field.CM31.square,lift,bind_tc_ok,h_m,h_m1,h_m2]
  exact ⟨_,rfl⟩

theorem cscale (self : C) (rhs : U32) : ∃ c,aspis_core.field.CM31.mul_m31 self rhs=ok c := by
  obtain ⟨m,h_m⟩ := PV_RunJoin_MaskScalarTotal69.mul self.a rhs
  obtain ⟨m1,h_m1⟩ := PV_RunJoin_MaskScalarTotal69.mul self.b rhs
  simp only [aspis_core.field.CM31.mul_m31,lift,bind_tc_ok,h_m,h_m1]
  exact ⟨_,rfl⟩

theorem cdouble (self : C) : ∃ c,aspis_core.field.CM31.double self=ok c := by
  obtain ⟨out,h_out⟩ := cadd self self
  simp only [aspis_core.field.CM31.double,lift,bind_tc_ok,h_out]
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

theorem qsquare (self : Q) : ∃ c,aspis_core.field.QM31.square self=ok c := by
  obtain ⟨c0_square,h_c0_square⟩ := csquare self.c0
  obtain ⟨c1_square,h_c1_square⟩ := csquare self.c1
  obtain ⟨c,h_c⟩ := mulR c1_square
  obtain ⟨c1,h_c1⟩ := cadd c0_square c
  obtain ⟨c2,h_c2⟩ := cmul self.c0 self.c1
  obtain ⟨c3,h_c3⟩ := cdouble c2
  simp only [aspis_core.field.QM31.square,lift,bind_tc_ok,h_c0_square,h_c1_square,h_c,h_c1,h_c2,h_c3]
  exact ⟨_,rfl⟩

theorem qscale (self : Q) (rhs : U32) : ∃ c,aspis_core.field.QM31.mul_m31 self rhs=ok c := by
  obtain ⟨c,h_c⟩ := cscale self.c0 rhs
  obtain ⟨c1,h_c1⟩ := cscale self.c1 rhs
  simp only [aspis_core.field.QM31.mul_m31,lift,bind_tc_ok,h_c,h_c1]
  exact ⟨_,rfl⟩

theorem hostR (value : C) : ∃ c,host_arithmetic.cm31_mul_r value=ok c := by
  obtain ⟨m,h_m⟩ := PV_RunJoin_MaskScalarTotal69.double value.a
  obtain ⟨m1,h_m1⟩ := PV_RunJoin_MaskScalarTotal69.sub m value.b
  obtain ⟨m2,h_m2⟩ := PV_RunJoin_MaskScalarTotal69.double value.b
  obtain ⟨m3,h_m3⟩ := PV_RunJoin_MaskScalarTotal69.add value.a m2
  obtain ⟨out,h_out⟩ := cnew m1 m3
  simp only [host_arithmetic.cm31_mul_r,lift,bind_tc_ok,h_m,h_m1,h_m2,h_m3,h_out]
  exact ⟨_,rfl⟩

theorem hostI (value : C) : ∃ c,host_arithmetic.cm31_mul_i value=ok c := by
  obtain ⟨m,h_m⟩ := PV_RunJoin_MaskScalarTotal69.neg value.b
  obtain ⟨out,h_out⟩ := cnew m value.a
  simp only [host_arithmetic.cm31_mul_i,lift,bind_tc_ok,h_m,h_out]
  exact ⟨_,rfl⟩

#print axioms cnew

#print axioms cadd
#print axioms csub
#print axioms cmul
#print axioms csquare
#print axioms cscale
#print axioms cdouble
#print axioms mulR
#print axioms qadd
#print axioms qmul
#print axioms qsquare
#print axioms qscale
#print axioms hostR
#print axioms hostI
end R1Z.PV_RunJoin_MaskFieldTotal69
