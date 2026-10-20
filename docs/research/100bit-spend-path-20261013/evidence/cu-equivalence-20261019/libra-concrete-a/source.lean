import CuSavingsLibraSourceModel
import CuSavingsWideMul
import CuSavingsWideMixed
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

def shared : AspisR1Libra.Shared where
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
  simp only [AspisR1Libra.field.wide_exact.WideExact.add,shared,hz,bind_tc_ok]

theorem mul (a b : L.E) (ha : canonicalE a) (hb : canonicalE b) :
    ∃ out, AspisR1Libra.field.wide_exact.WideExact.mul a b=.ok out ∧
      canonicalE out ∧ decodeEL out=decodeEL a*decodeEL b := by
  obtain ⟨z,hz,hc,hv⟩ := CuSavingsWideArithmetic.mul (toE a) (toE b) ha hb
  refine ⟨fromE z,?_,hc,hv⟩
  simp only [AspisR1Libra.field.wide_exact.WideExact.mul,shared,hz,bind_tc_ok]

theorem mixed (a : L.E) (q : L.K) (ha : canonicalE a) (hq : canonicalK q) :
    ∃ out, AspisR1Libra.field.wide_exact.WideExact.mul_qm31 a q=.ok out ∧
      canonicalE out ∧ decodeEL out=decodeEL a*embedding (decodeKL q) := by
  obtain ⟨z,hz,hc,hv⟩ := CuSavingsWideArithmetic.mixed (toE a) (toK q) ha hq
  refine ⟨fromE z,?_,hc,hv⟩
  simp only [AspisR1Libra.field.wide_exact.WideExact.mul_qm31,shared,hz,bind_tc_ok]

theorem kmul (a b : L.K) (ha : canonicalK a) (hb : canonicalK b) :
    ∃ out, AspisR1Libra.field.QM31.mul a b=.ok out ∧
      canonicalK out ∧ decodeKL out=decodeKL a*decodeKL b := by
  obtain ⟨z,hz,hc,hv⟩ := CuSavingsWideArithmetic.k_mul (toK a) (toK b) ha hb
  refine ⟨fromK z,?_,hc,hv⟩
  simp only [AspisR1Libra.field.QM31.mul,shared,hz,bind_tc_ok]

theorem injective (a b : L.E) (ha : canonicalE a) (hb : canonicalE b)
    (h : decodeEL a=decodeEL b) : a=b := by
  have he := CuSavingsWideArithmetic.injective (toE a) (toE b) ha hb h
  exact congrArg fromE he

#print axioms shared
#print axioms add
#print axioms mul
#print axioms mixed
#print axioms kmul
#print axioms injective
end AspisR1.CuSavingsLibraConcrete
