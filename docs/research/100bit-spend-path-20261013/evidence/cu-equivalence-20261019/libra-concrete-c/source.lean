import CuSavingsLibraSourceModel
import CuSavingsWideMul
import CuSavingsWideMixed
import CuSavingsWideScalar
set_option autoImplicit false
namespace AspisR1.CuSavingsLibraConcrete
open Aeneas Aeneas.Std Result
namespace L
abbrev K := AspisR1Libra.field.QM31
abbrev E := AspisR1Libra.field.wide_exact.WideExact
end L
open CuSavingsWideArithmetic

def toK (q : L.K) : K := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def fromK (q : K) : L.K := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def toE (e : L.E) : E := ⟨toK e.c0,toK e.c1⟩
def fromE (e : E) : L.E := ⟨fromK e.c0,fromK e.c1⟩
@[simp] theorem to_fromK (q : K) : toK (fromK q)=q := rfl
@[simp] theorem from_toK (q : L.K) : fromK (toK q)=q := rfl
@[simp] theorem to_fromE (e : E) : toE (fromE e)=e := rfl
@[simp] theorem from_toE (e : L.E) : fromE (toE e)=e := rfl

@[reducible] def shared : AspisR1Libra.Shared where
  add x y := do let z ← AspisR1WideArithmetic.field.wide_exact.WideExact.add (toE x) (toE y); .ok (fromE z)
  mul x y := do let z ← AspisR1WideArithmetic.field.wide_exact.WideExact.mul (toE x) (toE y); .ok (fromE z)
  mulK x q := do let z ← AspisR1WideArithmetic.field.wide_exact.WideExact.mul_qm31 (toE x) (toK q); .ok (fromE z)
  mulM x q := do let z ← AspisR1WideArithmetic.field.wide_exact.WideExact.mul_m31 (toE x) q; .ok (fromE z)
  kMul x y := do let z ← AspisR1WideArithmetic.field.QM31.mul (toK x) (toK y); .ok (fromK z)
  kSquare x := do let z ← AspisR1WideArithmetic.field.QM31.square (toK x); .ok (fromK z)

attribute [local instance] shared

def canonicalK (q : L.K) : Prop := CanonicalK (toK q)
def canonicalE (e : L.E) : Prop := CanonicalE (toE e)
def decodeKL (q : L.K) : ExactK := decodeK (toK q)
def decodeEL (e : L.E) : ExactE := decodeE (toE e)

theorem add (a b : L.E) (ha : canonicalE a) (hb : canonicalE b) :
    ∃ out, AspisR1Libra.field.wide_exact.WideExact.add a b=.ok out ∧
      canonicalE out ∧ decodeEL out=decodeEL a+decodeEL b := by
  obtain ⟨z,hz,hc,hv⟩ := CuSavingsWideArithmetic.add (toE a) (toE b) ha hb
  refine ⟨fromE z,?_,hc,hv⟩
  change (do let out ← AspisR1WideArithmetic.field.wide_exact.WideExact.add (toE a) (toE b); .ok (fromE out))=.ok (fromE z)
  simp only [hz,bind_tc_ok]

theorem mul (a b : L.E) (ha : canonicalE a) (hb : canonicalE b) :
    ∃ out, AspisR1Libra.field.wide_exact.WideExact.mul a b=.ok out ∧
      canonicalE out ∧ decodeEL out=decodeEL a*decodeEL b := by
  obtain ⟨z,hz,hc,hv⟩ := CuSavingsWideArithmetic.mul (toE a) (toE b) ha hb
  refine ⟨fromE z,?_,hc,hv⟩
  change (do let out ← AspisR1WideArithmetic.field.wide_exact.WideExact.mul (toE a) (toE b); .ok (fromE out))=.ok (fromE z)
  simp only [hz,bind_tc_ok]

theorem mixed (a : L.E) (q : L.K) (ha : canonicalE a) (hq : canonicalK q) :
    ∃ out, AspisR1Libra.field.wide_exact.WideExact.mul_qm31 a q=.ok out ∧
      canonicalE out ∧ decodeEL out=decodeEL a*embedding (decodeKL q) := by
  obtain ⟨z,hz,hc,hv⟩ := CuSavingsWideArithmetic.mixed (toE a) (toK q) ha hq
  refine ⟨fromE z,?_,hc,hv⟩
  change (do let out ← AspisR1WideArithmetic.field.wide_exact.WideExact.mul_qm31 (toE a) (toK q); .ok (fromE out))=.ok (fromE z)
  simp only [hz,bind_tc_ok]

theorem kmul (a b : L.K) (ha : canonicalK a) (hb : canonicalK b) :
    ∃ out, AspisR1Libra.field.QM31.mul a b=.ok out ∧
      canonicalK out ∧ decodeKL out=decodeKL a*decodeKL b := by
  obtain ⟨z,hz,hc,hv⟩ := CuSavingsWideArithmetic.k_mul (toK a) (toK b) ha hb
  refine ⟨fromK z,?_,hc,hv⟩
  change (do let out ← AspisR1WideArithmetic.field.QM31.mul (toK a) (toK b); .ok (fromK out))=.ok (fromK z)
  simp only [hz,bind_tc_ok]

theorem injective (a b : L.E) (ha : canonicalE a) (hb : canonicalE b)
    (h : decodeEL a=decodeEL b) : a=b := by
  have he := CuSavingsWideArithmetic.injective (toE a) (toE b) ha hb h
  exact congrArg fromE he

def quarter : ExactE := embedding (scalarK AspisR1Libra.QUARTER)

theorem scalar (a : L.E) (ha : canonicalE a) :
    ∃ out, AspisR1Libra.field.wide_exact.WideExact.mul_m31 a AspisR1Libra.QUARTER=.ok out ∧
      canonicalE out ∧ decodeEL out=decodeEL a*quarter := by
  have hq : AspisR1Libra.QUARTER.val<2147483647 := by simp [AspisR1Libra.QUARTER]
  obtain ⟨z,hz,hc,hv⟩ := CuSavingsWideArithmetic.scalar (toE a) AspisR1Libra.QUARTER hq
  refine ⟨fromE z,?_,hc,hv⟩
  change (do let out ← AspisR1WideArithmetic.field.wide_exact.WideExact.mul_m31 (toE a) AspisR1Libra.QUARTER; .ok (fromE out))=.ok (fromE z)
  simp only [hz,bind_tc_ok]

theorem square (a : L.K) (ha : canonicalK a) :
    ∃ out, AspisR1Libra.field.QM31.square a=.ok out ∧
      canonicalK out ∧ decodeKL out=(decodeKL a)^2 := by
  obtain ⟨z,hz,hc,hv⟩ := CuSavingsWideArithmetic.k_square (toK a) ha
  refine ⟨fromK z,?_,hc,?_⟩
  · change (do let out ← AspisR1WideArithmetic.field.QM31.square (toK a); .ok (fromK out))=.ok (fromK z)
    simp only [hz,bind_tc_ok]
  · simpa only [pow_two] using hv

theorem zero_canonical : canonicalE AspisR1Libra.field.wide_exact.WideExact.ZERO := by
  decide

theorem zero_value : decodeEL AspisR1Libra.field.wide_exact.WideExact.ZERO=0 := by
  simp [decodeEL,toE,toK,decodeE,decodeK,ExtractedCurrentQM31Exact.decode,
    AspisR1Libra.field.wide_exact.WideExact.ZERO,AspisR1Libra.field.QM31.ZERO,
    AspisR1WideArithmetic.toK,AspisR1WideArithmetic.toC]

theorem one_canonical : canonicalK AspisR1Libra.field.QM31.ONE := by
  decide

theorem one_value : decodeKL AspisR1Libra.field.QM31.ONE=1 := by
  simp [decodeKL,toK,decodeK,ExtractedCurrentQM31Exact.decode,
    AspisR1Libra.field.QM31.ONE,AspisR1WideArithmetic.toK,AspisR1WideArithmetic.toC]

def arithmetic : CuSavingsLibraSourceModel.Arithmetic ExactE ExactK where
  canonicalE := canonicalE
  canonicalK := canonicalK
  decodeE := decodeEL
  decodeK := decodeKL
  embedding := embedding
  quarter := quarter
  zero := zero_canonical
  zero_value := zero_value
  one := one_canonical
  one_value := one_value
  add := add
  mul := mul
  mixed := mixed
  scalar := scalar
  kmul := kmul
  square := square
  injective := injective

#print axioms scalar
#print axioms square
#print axioms zero_canonical
#print axioms zero_value
#print axioms one_canonical
#print axioms one_value
#print axioms arithmetic
#print axioms shared
#print axioms add
#print axioms mul
#print axioms mixed
#print axioms kmul
#print axioms injective
end AspisR1.CuSavingsLibraConcrete
