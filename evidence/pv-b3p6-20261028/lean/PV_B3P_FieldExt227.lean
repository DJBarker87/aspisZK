import PV_B3P_FieldBase227
import PV_B3P_E227_03
namespace PV_B3P_FieldExt227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
abbrev C := aspis_core.field.CM31
abbrev Q := aspis_core.field.QM31
open PV_B3P_FieldBase227

def cadd (x y : C) : C := ⟨add x.a y.a,add x.b y.b⟩
def csub (x y : C) : C := ⟨sub x.a y.a,sub x.b y.b⟩
def cmul (x y : C) : C :=
  let m0 := mul x.a y.a
  let m1 := mul x.b y.b
  let sx := U64.wrapping_add (core.convert.num.FromU64U32.from x.a) (core.convert.num.FromU64U32.from x.b)
  let sy := U64.wrapping_add (core.convert.num.FromU64U32.from y.a) (core.convert.num.FromU64U32.from y.b)
  let m2 := reduce (U64.wrapping_mul sx sy)
  ⟨sub m0 m1,sub (sub m2 m0) m1⟩
def csquare (x : C) : C :=
  let a := core.convert.num.FromU64U32.from x.a
  let b := core.convert.num.FromU64U32.from x.b
  let p := core.convert.num.FromU64U32.from aspis_core.field.P
  let m := reduce (U64.wrapping_mul (U64.wrapping_add a b) (U64.wrapping_sub (U64.wrapping_add a p) b))
  let ab := mul x.a x.b
  ⟨m,add ab ab⟩
def cmul_m31 (x : C) (y : U32) : C := ⟨mul x.a y,mul x.b y⟩
def cr (x : C) : C := ⟨sub (add x.a x.a) x.b,add x.a (add x.b x.b)⟩
def qadd (x y : Q) : Q := ⟨cadd x.c0 y.c0,cadd x.c1 y.c1⟩
def qsub (x y : Q) : Q := ⟨csub x.c0 y.c0,csub x.c1 y.c1⟩
def qmul (x y : Q) : Q :=
  let m0 := cmul x.c0 y.c0
  let m1 := cmul x.c1 y.c1
  let m2 := cmul (cadd x.c0 x.c1) (cadd y.c0 y.c1)
  ⟨cadd m0 (cr m1),csub (csub m2 m0) m1⟩
def qsquare (x : Q) : Q :=
  ⟨cadd (csquare x.c0) (cr (csquare x.c1)),cadd (cmul x.c0 x.c1) (cmul x.c0 x.c1)⟩
def qmul_m31 (x : Q) (y : U32) : Q := ⟨cmul_m31 x.c0 y,cmul_m31 x.c1 y⟩

theorem cadd_result (x y : C) : aspis_core.field.CM31.add x y = .ok (cadd x y) := rfl
theorem csub_result (x y : C) : aspis_core.field.CM31.sub x y = .ok (csub x y) := rfl
theorem cmul_result (x y : C) : aspis_core.field.CM31.mul x y = .ok (cmul x y) := rfl
theorem csquare_result (x : C) : aspis_core.field.CM31.square x = .ok (csquare x) := rfl
theorem cmul_m31_result (x : C) (y : U32) : aspis_core.field.CM31.mul_m31 x y = .ok (cmul_m31 x y) := rfl
theorem cr_result (x : C) : aspis_core.field.mul_by_r x = .ok (cr x) := rfl
theorem qadd_result (x y : Q) : aspis_core.field.QM31.add x y = .ok (qadd x y) := rfl
theorem qsub_result (x y : Q) : aspis_core.field.QM31.sub x y = .ok (qsub x y) := rfl
theorem qmul_result (x y : Q) : aspis_core.field.QM31.mul x y = .ok (qmul x y) := rfl
theorem qsquare_result (x : Q) : aspis_core.field.QM31.square x = .ok (qsquare x) := rfl
theorem qmul_m31_result (x : Q) (y : U32) : aspis_core.field.QM31.mul_m31 x y = .ok (qmul_m31 x y) := rfl

#print axioms cadd_result
#print axioms csub_result
#print axioms cmul_result
#print axioms csquare_result
#print axioms cmul_m31_result
#print axioms cr_result
#print axioms qadd_result
#print axioms qsub_result
#print axioms qmul_result
#print axioms qsquare_result
#print axioms qmul_m31_result
end PV_B3P_FieldExt227
