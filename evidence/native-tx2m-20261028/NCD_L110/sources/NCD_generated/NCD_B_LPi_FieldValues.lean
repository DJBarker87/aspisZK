-- Inherited body, import-only deployed-cohort retarget.
import NCD_B_LPi_CMProduct
set_option autoImplicit false
namespace AspisR1.LPi_FieldValues
open Aeneas Aeneas.Std Result
abbrev NC := LPi_CMProduct.NC
abbrev NQ := LPi_Total.NQ
abbrev NE := LPi_Total.NE
abbrev CW := Nat × Nat
abbrev QW := CW × CW
abbrev EW := QW × QW
def cw (x : NC) : CW := (x.a.val,x.b.val)
def qw (x : NQ) : QW := (cw x.c0,cw x.c1)
def ew (x : NE) : EW := (qw x.c0,qw x.c1)
def canonC := LPi_CMProduct.Canon
def canonQ (x : NQ) : Prop := canonC x.c0 ∧ canonC x.c1
def canonE (x : NE) : Prop := canonQ x.c0 ∧ canonQ x.c1
def addM (a b : Nat) := (a+b)%2147483647
def subM (a b : Nat) := (a+2147483647-b)%2147483647
def addC (a b : CW) : CW := (addM a.1 b.1,addM a.2 b.2)
def subC (a b : CW) : CW := (subM a.1 b.1,subM a.2 b.2)
def mulC (a b : CW) : CW := (LPi_CMProduct.realWord a.1 a.2 b.1 b.2,
  LPi_CMProduct.imagWord a.1 a.2 b.1 b.2)
def byR (a : CW) : CW := (subM (addM a.1 a.1) a.2,addM a.1 (addM a.2 a.2))
def addQ (a b : QW) : QW := (addC a.1 b.1,addC a.2 b.2)
def subQ (a b : QW) : QW := (subC a.1 b.1,subC a.2 b.2)
def mulQ (a b : QW) : QW :=
  let ac := mulC a.1 b.1
  let bd := mulC a.2 b.2
  let cross := mulC (addC a.1 a.2) (addC b.1 b.2)
  (addC ac (byR bd),subC (subC cross ac) bd)
def mulU (a : QW) : QW := (byR a.2,a.1)
def mulE (a b : EW) : EW :=
  let ac := mulQ a.1 b.1
  let bd := mulQ a.2 b.2
  let cross := mulQ (addQ a.1 a.2) (addQ b.1 b.2)
  (addQ ac (mulU bd),subQ (subQ cross ac) bd)

theorem cm_mul (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.mul x y = ok z ∧ canonC z ∧
      cw z = mulC (cw x) (cw y) := by
  obtain ⟨z,h,c,a,b⟩ := LPi_CMProduct.source x y hx hy
  exact ⟨z,h,c,Prod.ext a b⟩

theorem cm_add (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.add x y = ok z ∧ canonC z ∧
      cw z = addC (cw x) (cw y) := by
  obtain ⟨a,ha,va,ca⟩ := LPi_NatBase.add x.a y.a hx.1 hy.1
  obtain ⟨b,hb,vb,cb⟩ := LPi_NatBase.add x.b y.b hx.2 hy.2
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.CM31.add,ha,hb,bind_tc_ok],
    ⟨ca,cb⟩,Prod.ext va vb⟩

theorem cm_sub (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.sub x y = ok z ∧ canonC z ∧
      cw z = subC (cw x) (cw y) := by
  obtain ⟨a,ha,va,ca⟩ := LPi_NatBase.sub x.a y.a hx.1 hy.1
  obtain ⟨b,hb,vb,cb⟩ := LPi_NatBase.sub x.b y.b hx.2 hy.2
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.CM31.sub,ha,hb,bind_tc_ok],
    ⟨ca,cb⟩,Prod.ext va vb⟩

theorem by_r (x : NC) (hx : canonC x) :
    ∃ z, FIo_Native.aspis_core.field.mul_by_r x = ok z ∧ canonC z ∧ cw z = byR (cw x) := by
  obtain ⟨a,ha,va,ca⟩ := LPi_NatBase.add x.a x.a hx.1 hx.1
  obtain ⟨b,hb,vb,cb⟩ := LPi_NatBase.sub a x.b ca hx.2
  obtain ⟨c,hc,vc,cc⟩ := LPi_NatBase.add x.b x.b hx.2 hx.2
  obtain ⟨d,hd,vd,cd⟩ := LPi_NatBase.add x.a c hx.1 cc
  refine ⟨⟨b,d⟩,?_,⟨cb,cd⟩,?_⟩
  · simp only [FIo_Native.aspis_core.field.mul_by_r,FIo_Native.aspis_core.field.M31.double,
      ha,hb,hc,hd,bind_tc_ok]
  · exact Prod.ext (by simpa only [cw,byR,addM,subM,va] using vb) (by simpa only [cw,byR,addM,subM,vc] using vd)

#print axioms cm_mul
#print axioms cm_add
#print axioms cm_sub
#print axioms by_r
end AspisR1.LPi_FieldValues
