import CuSavingsLibraFactoredLoop
import CuSavingsLibraReferenceLiteral
import CuSavingsLibraReferenceConcrete
import CuSavingsLibraSourceProjection
set_option autoImplicit false
namespace AspisR1.CuSavingsLibraCandidate14
open Aeneas Aeneas.Std Result AspisR1Libra
open CuSavingsLibraSourceModel CuSavingsLibraSourceControl
open CuSavingsLibraSourceFactored CuSavingsLibraSourcePrepare
section Generic
variable {R S : Type} [CommSemiring R] [CommSemiring S] [Shared]

/-- Exact old/new helper equality after the unchanged caller's low-tensor
construction. The local arithmetic interface is discharged by the concrete
source instance in the production specialization. -/
theorem kernel_equivalence (A : Arithmetic R S) (ap0 ap1 : Points)
    (low : Array E 16#usize) (extra : Array K 2#usize)
    (hp0 : ∀ i, i<4 → A.canonicalE (lookup ap0 field.wide_exact.WideExact.ZERO i))
    (hp1 : ∀ i, i<4 → A.canonicalE (lookup ap1 field.wide_exact.WideExact.ZERO i))
    (hlow : ∀ i, i<16 → A.canonicalE (lookup low field.wide_exact.WideExact.ZERO i))
    (hextra : ∀ i, i<2 → A.canonicalK (lookup extra field.QM31.ONE i))
    (hvalues : ∀ i, i<16 → A.decodeE (lookup low field.wide_exact.WideExact.ZERO i)=
      CuSavingsLibra.literalLow (point A ap0) (point A ap1) A.quarter i) :
    new.factored_s2_libra_weights ap0 ap1 extra=old.twofold_libra_weights low extra := by
  obtain ⟨optimized,hoptimized,hoptCanonical,hoptValues⟩ :=
    CuSavingsLibraFactoredLoop.source_success A ap0 ap1 extra hp0 hp1 hextra
  obtain ⟨reference,hreference,hrefValues⟩ :=
    CuSavingsLibraReferenceLiteral.source_success A low extra (point A ap0) (point A ap1)
      A.quarter hlow hextra hvalues
  have equal : optimized=reference := by
    apply Subtype.ext
    apply List.ext_getElem
    · rw [optimized.property,reference.property]
    · intro j hj _
      have h4 : j<4 := by simpa only [optimized.property,show (4#usize).val=4 by scalar_tac] using hj
      have hopt := And.intro (hoptCanonical j h4) (hoptValues j h4)
      have href := hrefValues j h4
      have hv : CuSavingsLibraFactoredLoop.value A ap0 ap1 extra j=
          CuSavingsLibra.literalBlock (point A ap0) (point A ap1) A.quarter
            (CuSavingsLibraReferenceLiteral.challenge A extra 0)
            (CuSavingsLibraReferenceLiteral.challenge A extra 1) j := by
        unfold CuSavingsLibraFactoredLoop.value
        rw [CuSavingsLibra.factored_eq_literal]
        have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
        rcases hc with rfl | rfl | rfl | rfl <;> rfl
      have he := A.injective _ _ hopt.1 href.1 (hopt.2.trans (hv.trans href.2.symm))
      have hlenO : j<optimized.val.length := hj
      have hlenR : j<reference.val.length := by scalar_tac
      simpa only [lookup,List.getD_eq_getElem optimized.val field.wide_exact.WideExact.ZERO hlenO,
        List.getD_eq_getElem reference.val field.wide_exact.WideExact.ZERO hlenR] using he
  rw [hoptimized,hreference,equal]

end Generic

section Production
attribute [local instance] CuSavingsLibraConcrete.shared
open CuSavingsLibraConcrete

/-- The optimized call retains the caller's original low construction, used
also by the inactive-row path. This does not modify checkpoint encoding. -/
def optimized (ap0 ap1 : Points) (extra : Array K 2#usize) : Result (Array E 4#usize) := do
  let _ ← CuSavingsLibraCaller.lowCaller ap0 ap1
  new.factored_s2_libra_weights ap0 ap1 extra

theorem production_equivalence (ap0 ap1 : Points) (extra : Array K 2#usize)
    (hp0 : ∀ i, i<4 → canonicalE (lookup ap0 field.wide_exact.WideExact.ZERO i))
    (hp1 : ∀ i, i<4 → canonicalE (lookup ap1 field.wide_exact.WideExact.ZERO i))
    (hextra : ∀ i, i<2 → canonicalK (lookup extra field.QM31.ONE i)) :
    optimized ap0 ap1 extra=CuSavingsLibraReferenceConcrete.reference ap0 ap1 extra := by
  obtain ⟨low,hlow,hvalues⟩ := CuSavingsLibraCaller.low_success ap0 ap1 hp0 hp1
  have hc : ∀ i, i<16 → arithmetic.canonicalE (lookup low field.wide_exact.WideExact.ZERO i) :=
    fun i hi => (hvalues i hi).1
  have hv : ∀ i, i<16 → arithmetic.decodeE (lookup low field.wide_exact.WideExact.ZERO i)=
      CuSavingsLibra.literalLow (point arithmetic ap0) (point arithmetic ap1) arithmetic.quarter i := by
    intro i hi
    change decodeEL (lookup low field.wide_exact.WideExact.ZERO i)=
      CuSavingsLibra.literalLow (CuSavingsLibraReferenceConcrete.point ap0)
        (CuSavingsLibraReferenceConcrete.point ap1) quarter i
    exact (hvalues i hi).2.trans (CuSavingsLibraReferenceConcrete.lowTerm_eq_literal ap0 ap1 i)
  unfold optimized CuSavingsLibraReferenceConcrete.reference
  rw [hlow]
  simp only [bind_tc_ok]
  exact kernel_equivalence arithmetic ap0 ap1 low extra hp0 hp1 hc hextra hv

/-- Every unchanged computational caller can surround this replacement with
its original common prefix and suffix, including their errors/divergence.
No separately extracted whole-transaction theorem is asserted here. -/
theorem caller_context {T U : Type} (ap0 ap1 : Points) (extra : Array K 2#usize)
    (hp0 : ∀ i, i<4 → canonicalE (lookup ap0 field.wide_exact.WideExact.ZERO i))
    (hp1 : ∀ i, i<4 → canonicalE (lookup ap1 field.wide_exact.WideExact.ZERO i))
    (hextra : ∀ i, i<2 → canonicalK (lookup extra field.QM31.ONE i))
    (before : Array E 16#usize → Result T)
    (after : Array E 16#usize → T → Array E 4#usize → Result U) :
    (do
      let low ← CuSavingsLibraCaller.lowCaller ap0 ap1
      let common ← before low
      let result ← new.factored_s2_libra_weights ap0 ap1 extra
      after low common result) =
    (do
      let low ← CuSavingsLibraCaller.lowCaller ap0 ap1
      let common ← before low
      let result ← old.twofold_libra_weights low extra
      after low common result) := by
  obtain ⟨low,hlow,hvalues⟩ := CuSavingsLibraCaller.low_success ap0 ap1 hp0 hp1
  have hc : ∀ i, i<16 → arithmetic.canonicalE (lookup low field.wide_exact.WideExact.ZERO i) :=
    fun i hi => (hvalues i hi).1
  have hv : ∀ i, i<16 → arithmetic.decodeE (lookup low field.wide_exact.WideExact.ZERO i)=
      CuSavingsLibra.literalLow (point arithmetic ap0) (point arithmetic ap1) arithmetic.quarter i := by
    intro i hi
    change decodeEL (lookup low field.wide_exact.WideExact.ZERO i)=
      CuSavingsLibra.literalLow (CuSavingsLibraReferenceConcrete.point ap0)
        (CuSavingsLibraReferenceConcrete.point ap1) quarter i
    exact (hvalues i hi).2.trans (CuSavingsLibraReferenceConcrete.lowTerm_eq_literal ap0 ap1 i)
  have he := kernel_equivalence arithmetic ap0 ap1 low extra hp0 hp1 hc hextra hv
  simp only [hlow,bind_tc_ok]
  rw [he]

#print axioms production_equivalence
#print axioms caller_context
end Production

#print axioms kernel_equivalence
end AspisR1.CuSavingsLibraCandidate14
