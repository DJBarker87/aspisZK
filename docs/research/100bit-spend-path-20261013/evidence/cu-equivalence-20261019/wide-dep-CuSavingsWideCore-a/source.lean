import AspisR1WideArithmetic.Funs
import ExtractedCurrentQM31Exact
set_option autoImplicit false
namespace AspisR1.CuSavingsWideArithmetic
open Aeneas Aeneas.Std Result AspisR1WideArithmetic
abbrev K := field.QM31
abbrev E := field.wide_exact.WideExact
abbrev ExactK := AspisV8R15.ExactTowerBase.QM31Exact
abbrev CanonicalK (x : K) : Prop := ExtractedCurrentTowerAdd.CanonicalQM (toK x)
abbrev CanonicalE (x : E) : Prop := CanonicalK x.c0 ∧ CanonicalK x.c1
def decodeK (x : K) : ExactK := ExtractedCurrentQM31Exact.decode (toK x)
def U : ExactK := ⟨0,1⟩
abbrev ExactE := QuadraticAlgebra ExactK U 0
def decodeE (x : E) : ExactE := ⟨decodeK x.c0,decodeK x.c1⟩

theorem k_add (x y : K) (hx : CanonicalK x) (hy : CanonicalK y) :
    ∃ z, field.QM31.add x y=.ok z ∧ CanonicalK z ∧ decodeK z=decodeK x+decodeK y := by
  obtain ⟨z,hz,hc,hv⟩ := ExtractedCurrentQM31Exact.current_qm_add_exact (toK x) (toK y) hx hy
  refine ⟨fromK z,?_,hc,hv⟩
  simp only [field.QM31.add,hz,bind_tc_ok]

theorem k_mul (x y : K) (hx : CanonicalK x) (hy : CanonicalK y) :
    ∃ z, field.QM31.mul x y=.ok z ∧ CanonicalK z ∧ decodeK z=decodeK x*decodeK y := by
  obtain ⟨z,hz,hc,hv⟩ := ExtractedCurrentQM31Exact.current_qm_mul_exact (toK x) (toK y) hx hy
  refine ⟨fromK z,?_,hc,hv⟩
  simp only [field.QM31.mul,hz,bind_tc_ok]

theorem add (x y : E) (hx : CanonicalE x) (hy : CanonicalE y) :
    ∃ z, field.wide_exact.WideExact.add x y=.ok z ∧ CanonicalE z ∧ decodeE z=decodeE x+decodeE y := by
  obtain ⟨a,ha,hac,hav⟩ := k_add x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,hbc,hbv⟩ := k_add x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨a,b⟩,?_,⟨hac,hbc⟩,?_⟩
  · simp only [field.wide_exact.WideExact.add,ha,hb,bind_tc_ok]
  · apply QuadraticAlgebra.ext <;> assumption

#print axioms k_add
#print axioms k_mul
#print axioms add
end AspisR1.CuSavingsWideArithmetic
