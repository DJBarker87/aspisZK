import ExtractedCurrentQM31Exact
import R22TotalCheckedComposition

/-! Frozen backend arithmetic on canonical source words. The independent
modular/field refinement is imported, rather than replaced with a Kani stub
whose contract has not passed. R22 still requires its explicit operational
translation; this module does not manufacture a wrapping interpretation. -/
set_option autoImplicit false
namespace AspisR1.S7Kani2BackendArithmetic
open Aeneas Aeneas.Std Result
open ExtractedCurrentQM31Exact
open R22TotalCheckedComposition
abbrev Q := CurrentQM
abbrev Canonical := CurrentCanonicalQM
abbrev CanonicalPair := {xy : Q × Q // Canonical xy.1 ∧ Canonical xy.2}
def multiply (xy : CanonicalPair) : Result Q :=
  AspisR1Qm31ArithmeticProbe.field.QM31.mul xy.val.1 xy.val.2

/-- Both totality and decoded field multiplication, on the actual source
primitive and the canonical domain needed by the caller. -/
theorem multiply_exact (xy : CanonicalPair) :
    ∃ z, multiply xy = ok z ∧ Canonical z ∧
      decode z = decode xy.val.1 * decode xy.val.2 := by
  exact current_qm_mul_exact _ _ xy.property.1 xy.property.2

theorem multiply_R22 (translation : Translation multiply) :
    ∀ xy, NoOverflow (translation.code xy) ∧
      wrapping (translation.code xy) = multiply xy := by
  apply extracted_total_R22
  intro xy
  obtain ⟨z,hz,_,_⟩ := multiply_exact xy
  exact ⟨z,hz⟩

/-- Structural carrier for the two source WideExact components. This port
covers add and mixed multiplication, not the general E product or inverse. -/
structure Wide where
  c0 : Q
  c1 : Q
abbrev CanonicalWide (x : Wide) := Canonical x.c0 ∧ Canonical x.c1

def addWide (x y : Wide) : Result Wide := do
  let c0 ← AspisR1Qm31ArithmeticProbe.field.QM31.add x.c0 y.c0
  let c1 ← AspisR1Qm31ArithmeticProbe.field.QM31.add x.c1 y.c1
  ok ⟨c0,c1⟩

def mulWideCanonical (x : Wide) (y : Q) : Result Wide := do
  let c0 ← AspisR1Qm31ArithmeticProbe.field.QM31.mul x.c0 y
  let c1 ← AspisR1Qm31ArithmeticProbe.field.QM31.mul x.c1 y
  ok ⟨c0,c1⟩

/-- The two independent component additions in the literal WideExact body. -/
theorem addWide_exact (x y : Wide) (hx : CanonicalWide x) (hy : CanonicalWide y) :
    ∃ z, addWide x y = ok z ∧ CanonicalWide z ∧
      decode z.c0 = decode x.c0 + decode y.c0 ∧
      decode z.c1 = decode x.c1 + decode y.c1 := by
  obtain ⟨a,ha,ca,va⟩ := current_qm_add_exact _ _ hx.1 hy.1
  obtain ⟨b,hb,cb,vb⟩ := current_qm_add_exact _ _ hx.2 hy.2
  exact ⟨⟨a,b⟩,by simp only [addWide,ha,hb,bind_tc_ok],⟨ca,cb⟩,va,vb⟩

/-- Mixed multiplication after the source rhs canonicalisation. The caller
must establish the canonical input or supply the canonicalisation join. -/
theorem mulWideCanonical_exact (x : Wide) (y : Q)
    (hx : CanonicalWide x) (hy : Canonical y) :
    ∃ z, mulWideCanonical x y = ok z ∧ CanonicalWide z ∧
      decode z.c0 = decode x.c0 * decode y ∧
      decode z.c1 = decode x.c1 * decode y := by
  obtain ⟨a,ha,ca,va⟩ := current_qm_mul_exact _ _ hx.1 hy
  obtain ⟨b,hb,cb,vb⟩ := current_qm_mul_exact _ _ hx.2 hy
  exact ⟨⟨a,b⟩,by simp only [mulWideCanonical,ha,hb,bind_tc_ok],⟨ca,cb⟩,va,vb⟩

#print axioms multiply_exact
#print axioms multiply_R22
#print axioms addWide_exact
#print axioms mulWideCanonical_exact
end AspisR1.S7Kani2BackendArithmetic
