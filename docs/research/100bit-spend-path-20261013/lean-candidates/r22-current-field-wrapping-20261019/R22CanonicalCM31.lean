import R22CanonicalM31AddSub
import R22CurrentReducerMul
import ExtractedCurrentCM31Mul

/-! Exact checked/wrapping equality for the current CM31 tower operations,
using existing source-shaped cross-product and canonicality proofs. -/
set_option autoImplicit false
namespace AspisR1.R22CanonicalCM31
open Aeneas Aeneas.Std Result
open CheckedWrappingScalarAgreement ExtractedCurrentReducerOps
open R22CanonicalM31AddSub R22CurrentReducerMul ExtractedCurrentTowerAdd
abbrev CM := AspisR1Qm31ArithmeticProbe.field.CM31

def wrappingCMAdd (x y : CM) : CM := ⟨wrappingAdd x.a y.a,wrappingAdd x.b y.b⟩
def wrappingCMSub (x y : CM) : CM := ⟨wrappingSub x.a y.a,wrappingSub x.b y.b⟩

theorem cm_add_agrees (x y : CM) (hx : CanonicalCM x) (hy : CanonicalCM y) :
    AspisR1Qm31ArithmeticProbe.field.CM31.add x y = ok (wrappingCMAdd x y) := by
  simp only [AspisR1Qm31ArithmeticProbe.field.CM31.add,
    canonical_add_agrees _ _ hx.1 hy.1,canonical_add_agrees _ _ hx.2 hy.2,
    bind_tc_ok,wrappingCMAdd]

theorem cm_sub_agrees (x y : CM) (hx : CanonicalCM x) (hy : CanonicalCM y) :
    AspisR1Qm31ArithmeticProbe.field.CM31.sub x y = ok (wrappingCMSub x y) := by
  simp only [AspisR1Qm31ArithmeticProbe.field.CM31.sub,
    canonical_sub_agrees _ _ hx.1 hy.1,canonical_sub_agrees _ _ hx.2 hy.2,
    bind_tc_ok,wrappingCMSub]

theorem cm_add_canonical (x y : CM) (hx : CanonicalCM x) (hy : CanonicalCM y) :
    CanonicalCM (wrappingCMAdd x y) :=
  ⟨wrapping_add_canonical _ _ hx.1 hy.1,wrapping_add_canonical _ _ hx.2 hy.2⟩
theorem cm_sub_canonical (x y : CM) (hx : CanonicalCM x) (hy : CanonicalCM y) :
    CanonicalCM (wrappingCMSub x y) :=
  ⟨wrapping_sub_canonical _ _ hx.1 hy.1,wrapping_sub_canonical _ _ hx.2 hy.2⟩

def widen (x : U32) : U64 := core.convert.num.FromU64U32.from x
def wrappingCross (x y : CM) : U64 :=
  UScalar.wrapping_mul (UScalar.wrapping_add (widen x.a) (widen x.b))
    (UScalar.wrapping_add (widen y.a) (widen y.b))

theorem cross_agrees (x y : CM) (hx : CanonicalCM x) (hy : CanonicalCM y) :
    ExtractedCurrentCM31Mul.generatedCrossFragment x y = ok (wrappingCross x y) := by
  have hlbound : (widen x.a).val+(widen x.b).val < 2^64 := by
    simp only [widen,ExtractedCurrentCM31Mul.widen_value]
    have h1 := x.a.bv.isLt; have h2 := x.b.bv.isLt
    change x.a.val < 2^32 at h1; change x.b.val < 2^32 at h2
    omega
  have hrbound : (widen y.a).val+(widen y.b).val < 2^64 := by
    simp only [widen,ExtractedCurrentCM31Mul.widen_value]
    have h1 := y.a.bv.isLt; have h2 := y.b.bv.isLt
    change y.a.val < 2^32 at h1; change y.b.val < 2^32 at h2
    omega
  obtain ⟨l,hl,_⟩ := add_success _ _ hlbound
  obtain ⟨r,hr,_⟩ := add_success _ _ hrbound
  obtain ⟨p,hp,_⟩ := ExtractedCurrentCM31Mul.crossOperand_success x.a x.b y.a y.b
    hx.1 hx.2 hy.1 hy.2
  change (do let l ← UScalar.add (widen x.a) (widen x.b)
             let r ← UScalar.add (widen y.a) (widen y.b)
             UScalar.mul l r) = ok p at hp
  have hmul : UScalar.mul l r = ok p := by
    simpa only [hl,hr,bind_tc_ok] using hp
  have hwl := (add_success_agrees _ _ _ hl).1
  have hwr := (add_success_agrees _ _ _ hr).1
  have hwp := (mul_success_agrees _ _ _ hmul).1
  rw [ExtractedCurrentCM31Mul.generatedCrossFragment_eq]
  change (do let l ← UScalar.add (widen x.a) (widen x.b)
             let r ← UScalar.add (widen y.a) (widen y.b)
             UScalar.mul l r) = ok (wrappingCross x y)
  simp only [hl,hr,bind_tc_ok,wrappingCross,hwl,hwr,hwp,hmul]

def wrappingCMMul (x y : CM) : CM :=
  let m0 := wrappingMul x.a y.a
  let m1 := wrappingMul x.b y.b
  let m2 := wrappingReduce (wrappingCross x y)
  ⟨wrappingSub m0 m1,wrappingSub (wrappingSub m2 m0) m1⟩

theorem cm_mul_agrees (x y : CM) (hx : CanonicalCM x) (hy : CanonicalCM y) :
    AspisR1Qm31ArithmeticProbe.field.CM31.mul x y = ok (wrappingCMMul x y) := by
  have h0 := (wrapping_mul_mod x.a y.a).2
  have h1 := (wrapping_mul_mod x.b y.b).2
  have h2 := (wrapping_reduce_mod (wrappingCross x y)).2
  have hh := wrapping_sub_canonical _ _ h2 h0
  rw [ExtractedCurrentCM31Mul.generated_mul_graph]
  simp only [current_mul_agrees,cross_agrees x y hx hy,bind_tc_ok,
    AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64,current_reducer_agrees,
    canonical_sub_agrees _ _ h0 h1,canonical_sub_agrees _ _ h2 h0,
    canonical_sub_agrees _ _ hh h1,wrappingCMMul]

theorem cm_mul_canonical (x y : CM) (hx : CanonicalCM x) (hy : CanonicalCM y) :
    CanonicalCM (wrappingCMMul x y) := by
  obtain ⟨z,hz,hc,_,_⟩ := ExtractedCurrentCM31Mul.current_mul_words x y hx hy
  rw [cm_mul_agrees x y hx hy] at hz
  exact Result.ok.inj hz ▸ hc

#print axioms cm_add_agrees
#print axioms cm_sub_agrees
#print axioms cross_agrees
#print axioms cm_mul_agrees
#print axioms cm_mul_canonical
end AspisR1.R22CanonicalCM31
