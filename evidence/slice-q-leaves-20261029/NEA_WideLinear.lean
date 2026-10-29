import LPi_TowerValues
import NEA_CurrentProducts
import NEA_LinePrimitive
set_option autoImplicit false
namespace NEA_WideLinear
open Aeneas Aeneas.Std Result AspisR1.LPi_FieldValues
abbrev C := AspisR1CurrentWide.field.CM31
abbrev Q := AspisR1CurrentWide.field.QM31
abbrev E := AspisR1CurrentWide.field.wide_exact.WideExact
def cwC (x : C) : CW := (x.a.val,x.b.val)
def cwQ (x : Q) : QW := (cwC x.c0,cwC x.c1)
def cwE (x : E) : EW := (cwQ x.c0,cwQ x.c1)
def canonC' (x : C) : Prop := x.a.val<2147483647 ∧ x.b.val<2147483647
def canonQ' (x : Q) : Prop := canonC' x.c0 ∧ canonC' x.c1
def canonE' (x : E) : Prop := canonQ' x.c0 ∧ canonQ' x.c1
def addE (x y : EW) : EW := (addQ x.1 y.1,addQ x.2 y.2)
def subE (x y : EW) : EW := (subQ x.1 y.1,subQ x.2 y.2)
theorem add_cm (x y : C) (hx : canonC' x) (hy : canonC' y) :
    ∃ z, AspisR1CurrentWide.field.CM31.add x y=ok z ∧ canonC' z ∧ cwC z=addC (cwC x) (cwC y) := by
  obtain ⟨a,ha,va,ca⟩ := AspisR1.ExtractedCurrentM31AddSub.current_add_mod x.a y.a hx.1 hy.1
  obtain ⟨b,hb,vb,cb⟩ := AspisR1.ExtractedCurrentM31AddSub.current_add_mod x.b y.b hx.2 hy.2
  rw [← AspisR1CurrentWide.Proof.m31_add_same] at ha
  rw [← AspisR1CurrentWide.Proof.m31_add_same] at hb
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,Prod.ext va vb⟩
  simp only [AspisR1CurrentWide.field.CM31.add,ha,hb,bind_tc_ok]
theorem add_qm (x y : Q) (hx : canonQ' x) (hy : canonQ' y) :
    ∃ z, AspisR1CurrentWide.field.QM31.add x y=ok z ∧ canonQ' z ∧ cwQ z=addQ (cwQ x) (cwQ y) := by
  obtain ⟨a,ha,ca,va⟩ := add_cm x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,vb⟩ := add_cm x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,Prod.ext va vb⟩
  simp only [AspisR1CurrentWide.field.QM31.add,ha,hb,bind_tc_ok]
theorem add (x y : E) (hx : canonE' x) (hy : canonE' y) :
    ∃ z, AspisR1CurrentWide.field.wide_exact.WideExact.add x y=ok z ∧ canonE' z ∧ cwE z=addE (cwE x) (cwE y) := by
  obtain ⟨a,ha,ca,va⟩ := add_qm x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,vb⟩ := add_qm x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,Prod.ext va vb⟩
  simp only [AspisR1CurrentWide.field.wide_exact.WideExact.add,ha,hb,bind_tc_ok]
theorem sub_cm (x y : C) (hx : canonC' x) (hy : canonC' y) :
    ∃ z, AspisR1CurrentWide.field.CM31.sub x y=ok z ∧ canonC' z ∧ cwC z=subC (cwC x) (cwC y) := by
  obtain ⟨a,ha,va,ca⟩ := AspisR1.ExtractedCurrentM31AddSub.current_sub_mod x.a y.a hx.1 hy.1
  obtain ⟨b,hb,vb,cb⟩ := AspisR1.ExtractedCurrentM31AddSub.current_sub_mod x.b y.b hx.2 hy.2
  rw [← AspisR1CurrentWide.Proof.m31_sub_same] at ha
  rw [← AspisR1CurrentWide.Proof.m31_sub_same] at hb
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,Prod.ext va vb⟩
  simp only [AspisR1CurrentWide.field.CM31.sub,ha,hb,bind_tc_ok]
theorem sub_qm (x y : Q) (hx : canonQ' x) (hy : canonQ' y) :
    ∃ z, AspisR1CurrentWide.field.QM31.sub x y=ok z ∧ canonQ' z ∧ cwQ z=subQ (cwQ x) (cwQ y) := by
  obtain ⟨a,ha,ca,va⟩ := sub_cm x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,vb⟩ := sub_cm x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,Prod.ext va vb⟩
  simp only [AspisR1CurrentWide.field.QM31.sub,ha,hb,bind_tc_ok]
theorem sub (x y : E) (hx : canonE' x) (hy : canonE' y) :
    ∃ z, AspisR1CurrentWide.field.wide_exact.WideExact.sub x y=ok z ∧ canonE' z ∧ cwE z=subE (cwE x) (cwE y) := by
  obtain ⟨a,ha,ca,va⟩ := sub_qm x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,vb⟩ := sub_qm x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,Prod.ext va vb⟩
  simp only [AspisR1CurrentWide.field.wide_exact.WideExact.sub,ha,hb,bind_tc_ok]
theorem add_branch (x y : Nat) (hx : x<2147483647) (hy : y<2147483647) :
    addM x y = if x+y≥2147483647 then x+y-2147483647 else x+y := by
  unfold addM
  split
  · rw [← Nat.mod_add_div (x+y) 2147483647]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]

theorem sub_branch (x y : Nat) (hx : x<2147483647) (hy : y<2147483647) :
    subM x y = if x≥y then x-y else 2147483647-y+x := by
  unfold subM
  split
  · have e : x+2147483647-y=(x-y)+2147483647 := by omega
    rw [e,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega
#print axioms add_cm
#print axioms add_qm
#print axioms add
#print axioms sub_cm
#print axioms sub_qm
#print axioms sub
#print axioms add_branch
#print axioms sub_branch
end NEA_WideLinear
