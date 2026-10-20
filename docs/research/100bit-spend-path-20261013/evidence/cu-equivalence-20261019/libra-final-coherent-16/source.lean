import CuSavingsLibraReferenceLiteral
import CuSavingsLibraCaller
set_option autoImplicit false
namespace AspisR1.CuSavingsLibraReferenceConcrete
open Aeneas Aeneas.Std Result AspisR1Libra
open CuSavingsLibraSourceControl CuSavingsLibraConcrete
open CuSavingsLibraCaller (Points)
attribute [local instance] CuSavingsLibraConcrete.shared

def point (p : Points) (i : Nat) : CuSavingsWideArithmetic.ExactE :=
  decodeEL (lookup p field.wide_exact.WideExact.ZERO (CuSavingsLibraSourcePerm.perm i))

def challenge (extra : Array L.K 2#usize) (side : Nat) : CuSavingsWideArithmetic.ExactE :=
  CuSavingsLibraReferenceLiteral.challenge arithmetic extra side

theorem lowTerm_eq_literal (p q : Points) (i : Nat) :
    CuSavingsLibraCaller.lowTerm p q i=CuSavingsLibra.literalLow (point p) (point q) quarter i := by
  unfold CuSavingsLibraCaller.lowTerm CuSavingsLibra.literalLow point
  ring

def reference (p q : Points) (extra : Array L.K 2#usize) : Result (Array L.E 4#usize) := do
  let low ← CuSavingsLibraCaller.lowCaller p q
  old.twofold_libra_weights low extra

theorem source_success (p q : Points) (extra : Array L.K 2#usize)
    (hp : ∀ i,i<4 → canonicalE (lookup p field.wide_exact.WideExact.ZERO i))
    (hq : ∀ i,i<4 → canonicalE (lookup q field.wide_exact.WideExact.ZERO i))
    (he : ∀ side,side<2 → canonicalK (lookup extra field.QM31.ONE side)) :
    ∃ weights : Array L.E 4#usize,reference p q extra=.ok weights ∧
      ∀ j,j<4 → canonicalE (lookup weights field.wide_exact.WideExact.ZERO j) ∧
        decodeEL (lookup weights field.wide_exact.WideExact.ZERO j)=
          CuSavingsLibra.literalBlock (point p) (point q) quarter (challenge extra 0) (challenge extra 1) j := by
  obtain ⟨low,hlow,hvalues⟩ := CuSavingsLibraCaller.low_success p q hp hq
  have hlowC : ∀ i,i<16 → arithmetic.canonicalE (lookup low field.wide_exact.WideExact.ZERO i) :=
    fun i hi => (hvalues i hi).1
  have hlowV : ∀ i,i<16 → arithmetic.decodeE (lookup low field.wide_exact.WideExact.ZERO i)=
      CuSavingsLibra.literalLow (point p) (point q) quarter i := by
    intro i hi
    exact (hvalues i hi).2.trans (lowTerm_eq_literal p q i)
  obtain ⟨weights,hweights,hresult⟩ := CuSavingsLibraReferenceLiteral.source_success
    arithmetic low extra (point p) (point q) quarter hlowC he hlowV
  refine ⟨weights,?_,hresult⟩
  unfold reference
  rw [hlow]
  simpa only [bind_tc_ok] using hweights

def values (weights : Array L.E 4#usize) : CuSavingsWideArithmetic.ExactE × CuSavingsWideArithmetic.ExactE × CuSavingsWideArithmetic.ExactE × CuSavingsWideArithmetic.ExactE :=
  (decodeEL (lookup weights field.wide_exact.WideExact.ZERO 0),
   decodeEL (lookup weights field.wide_exact.WideExact.ZERO 1),
   decodeEL (lookup weights field.wide_exact.WideExact.ZERO 2),
   decodeEL (lookup weights field.wide_exact.WideExact.ZERO 3))

theorem source_values (p q : Points) (extra : Array L.K 2#usize)
    (hp : ∀ i,i<4 → canonicalE (lookup p field.wide_exact.WideExact.ZERO i))
    (hq : ∀ i,i<4 → canonicalE (lookup q field.wide_exact.WideExact.ZERO i))
    (he : ∀ side,side<2 → canonicalK (lookup extra field.QM31.ONE side)) :
    ∃ weights : Array L.E 4#usize,reference p q extra=.ok weights ∧
      (∀ j,j<4 → canonicalE (lookup weights field.wide_exact.WideExact.ZERO j)) ∧
      values weights=CuSavingsLibra.literalWeights (point p) (point q) quarter (challenge extra 0) (challenge extra 1) := by
  obtain ⟨weights,hweights,hvalues⟩ := source_success p q extra hp hq he
  refine ⟨weights,hweights,fun j hj => (hvalues j hj).1,?_⟩
  exact Prod.ext (hvalues 0 (by omega)).2
    (Prod.ext (hvalues 1 (by omega)).2 (Prod.ext (hvalues 2 (by omega)).2 (hvalues 3 (by omega)).2))

#print axioms lowTerm_eq_literal
#print axioms source_success
#print axioms source_values
end AspisR1.CuSavingsLibraReferenceConcrete
