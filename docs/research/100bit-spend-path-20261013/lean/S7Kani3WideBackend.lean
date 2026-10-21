import S7Kani3CanonicalBackend
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace AspisR1.S7Kani3WideBackend
open Aeneas Aeneas.Std Result
open ExtractedCurrentQM31Exact
open S7Kani2BackendArithmetic (Q Wide Canonical CanonicalWide)
open ExtractedCurrentTowerAdd (CanonicalCM)
abbrev CM := AspisR1Qm31ArithmeticProbe.field.CM31
abbrev C := AspisV8R15.ExactTowerBase.CM31Exact

def decodeCM (x : CM) : C := ⟨(x.a.val : M31Exact),(x.b.val : M31Exact)⟩

theorem cast_difference (a b : Nat) (hb : b<2147483647) :
    (((a+2147483647-b)%2147483647 : Nat) : M31Exact) =
      (a : M31Exact)-(b : M31Exact) := by
  rw [ZMod.natCast_mod, Nat.cast_sub (by omega),Nat.cast_add]
  simp [M31Exact]

theorem cm_sub_exact (x y : CM) (hx : CanonicalCM x) (hy : CanonicalCM y) :
    ∃ z, AspisR1Qm31ArithmeticProbe.field.CM31.sub x y=ok z ∧
      CanonicalCM z ∧ decodeCM z=decodeCM x-decodeCM y := by
  obtain ⟨z,hz,hcz,ha,hb⟩ := ExtractedCurrentTowerAdd.current_cm_sub_mod x y hx hy
  refine ⟨z,hz,hcz,?_⟩
  apply QuadraticAlgebra.ext <;>
    simp only [decodeCM]
  · rw [ha]; exact cast_difference _ _ hy.1
  · rw [hb]; exact cast_difference _ _ hy.2

/-- Additive port: QM31.sub was outside the inherited extraction selection. -/
def qmSub (x y : Q) : Result Q := do
  let a ← AspisR1Qm31ArithmeticProbe.field.CM31.sub x.c0 y.c0
  let b ← AspisR1Qm31ArithmeticProbe.field.CM31.sub x.c1 y.c1
  ok ⟨a,b⟩

theorem qm_sub_exact (x y : Q) (hx : Canonical x) (hy : Canonical y) :
    ∃ z, qmSub x y=ok z ∧
      Canonical z ∧ decode z=decode x-decode y := by
  obtain ⟨a,ha,hca,hda⟩ := cm_sub_exact x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,hcb,hdb⟩ := cm_sub_exact x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨a,b⟩,by simp only [qmSub,ha,hb,bind_tc_ok],⟨hca,hcb⟩,?_⟩
  apply QuadraticAlgebra.ext
  · exact hda
  · exact hdb

/-- The literal frozen mul_by_r implements (2+i) times its input. -/
theorem mul_r_exact (x : CM) (hx : CanonicalCM x) :
    ∃ z, AspisR1Qm31ArithmeticProbe.field.mul_by_r x=ok z ∧
      CanonicalCM z ∧
      (z.a.val : M31Exact)=2*(x.a.val : M31Exact)-(x.b.val : M31Exact) ∧
      (z.b.val : M31Exact)=(x.a.val : M31Exact)+2*(x.b.val : M31Exact) := by
  obtain ⟨a2,ha2,va2,ca2⟩ := ExtractedCurrentM31AddSub.current_add_mod x.a x.a hx.1 hx.1
  obtain ⟨a,ha,va,ca⟩ := ExtractedCurrentM31AddSub.current_sub_mod a2 x.b ca2 hx.2
  obtain ⟨b2,hb2,vb2,cb2⟩ := ExtractedCurrentM31AddSub.current_add_mod x.b x.b hx.2 hx.2
  obtain ⟨b,hb,vb,cb⟩ := ExtractedCurrentM31AddSub.current_add_mod x.a b2 hx.1 cb2
  refine ⟨⟨a,b⟩,by simp only [AspisR1Qm31ArithmeticProbe.field.mul_by_r,
    AspisR1Qm31ArithmeticProbe.field.M31.double,ha2,ha,hb2,hb,bind_tc_ok],⟨ca,cb⟩,?_,?_⟩
  · rw [va,cast_difference _ _ hx.2,va2]
    simp only [ZMod.natCast_mod,Nat.cast_add]
    ring
  · rw [vb,vb2]
    simp only [ZMod.natCast_mod,Nat.cast_add]
    ring

def mulU (x : Q) : Result Q := do
  let r ← AspisR1Qm31ArithmeticProbe.field.mul_by_r x.c1
  ok ⟨r,x.c0⟩
def u : QM31Exact := ⟨0,1⟩

theorem mul_u_exact (x : Q) (hx : Canonical x) :
    ∃ z, mulU x=ok z ∧ Canonical z ∧ decode z=u*decode x := by
  obtain ⟨r,hr,hcr,hra,hrb⟩ := mul_r_exact x.c1 hx.2
  refine ⟨⟨r,x.c0⟩,by simp only [mulU,hr,bind_tc_ok],⟨hcr,hx.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · simpa [decode,u,sub_eq_add_neg,add_comm] using hra
    · simpa [decode,u,sub_eq_add_neg,add_comm] using hrb
  · simp [decode,u]

def subWide (x y : Wide) : Result Wide := do
  let a ← qmSub x.c0 y.c0
  let b ← qmSub x.c1 y.c1
  ok ⟨a,b⟩

def mulWide (x y : Wide) : Result Wide := do
  let ac ← AspisR1Qm31ArithmeticProbe.field.QM31.mul x.c0 y.c0
  let bd ← AspisR1Qm31ArithmeticProbe.field.QM31.mul x.c1 y.c1
  let sx ← AspisR1Qm31ArithmeticProbe.field.QM31.add x.c0 x.c1
  let sy ← AspisR1Qm31ArithmeticProbe.field.QM31.add y.c0 y.c1
  let cross ← AspisR1Qm31ArithmeticProbe.field.QM31.mul sx sy
  let ubd ← mulU bd
  let c0 ← AspisR1Qm31ArithmeticProbe.field.QM31.add ac ubd
  let c1a ← qmSub cross ac
  let c1 ← qmSub c1a bd
  ok ⟨c0,c1⟩

theorem sub_wide_exact (x y : Wide) (hx : CanonicalWide x) (hy : CanonicalWide y) :
    ∃ z, subWide x y=ok z ∧ CanonicalWide z ∧
      decode z.c0=decode x.c0-decode y.c0 ∧ decode z.c1=decode x.c1-decode y.c1 := by
  obtain ⟨a,ha,hca,hda⟩ := qm_sub_exact x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,hcb,hdb⟩ := qm_sub_exact x.c1 y.c1 hx.2 hy.2
  exact ⟨⟨a,b⟩,by simp only [subWide,ha,hb,bind_tc_ok],⟨hca,hcb⟩,hda,hdb⟩

theorem mul_wide_exact (x y : Wide) (hx : CanonicalWide x) (hy : CanonicalWide y) :
    ∃ z, mulWide x y=ok z ∧ CanonicalWide z ∧
      decode z.c0=decode x.c0*decode y.c0+u*(decode x.c1*decode y.c1) ∧
      decode z.c1=decode x.c0*decode y.c1+decode x.c1*decode y.c0 := by
  obtain ⟨ac,hac,cac,vac⟩ := current_qm_mul_exact x.c0 y.c0 hx.1 hy.1
  obtain ⟨bd,hbd,cbd,vbd⟩ := current_qm_mul_exact x.c1 y.c1 hx.2 hy.2
  obtain ⟨sx,hsx,csx,vsx⟩ := current_qm_add_exact x.c0 x.c1 hx.1 hx.2
  obtain ⟨sy,hsy,csy,vsy⟩ := current_qm_add_exact y.c0 y.c1 hy.1 hy.2
  obtain ⟨cross,hcross,ccross,vcross⟩ := current_qm_mul_exact sx sy csx csy
  obtain ⟨ubd,hubd,cubd,vubd⟩ := mul_u_exact bd cbd
  obtain ⟨c0,hc0,cc0,vc0⟩ := current_qm_add_exact ac ubd cac cubd
  obtain ⟨c1a,hc1a,cc1a,vc1a⟩ := qm_sub_exact cross ac ccross cac
  obtain ⟨c1,hc1,cc1,vc1⟩ := qm_sub_exact c1a bd cc1a cbd
  refine ⟨⟨c0,c1⟩,by simp only [mulWide,hac,hbd,hsx,hsy,hcross,hubd,hc0,hc1a,hc1,bind_tc_ok],⟨cc0,cc1⟩,?_,?_⟩
  · simp only [vc0,vac,vubd,vbd]
  · simp only [vc1,vc1a,vcross,vsx,vsy,vac,vbd]
    ring

#print axioms cast_difference
#print axioms cm_sub_exact
#print axioms qm_sub_exact
#print axioms mul_r_exact
#print axioms mul_u_exact
#print axioms sub_wide_exact
#print axioms mul_wide_exact
end AspisR1.S7Kani3WideBackend
