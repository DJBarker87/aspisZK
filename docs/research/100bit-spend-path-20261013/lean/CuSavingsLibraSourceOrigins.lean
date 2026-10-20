import CuSavingsLibraOrigins
import CuSavingsLibraCandidate14
set_option autoImplicit false
namespace AspisR1.CuSavingsLibraSourceOrigins
open Aeneas Aeneas.Std Result
open CuSavingsLibraConcrete CuSavingsLibraOrigins CuSavingsLibraSourceControl
attribute [local instance] CuSavingsLibraConcrete.shared
variable [AspisR1CanonicalSampler.Shared] [AspisR1CanonicalReader.Runtime]
  [AspisR1CanonicalKReader.Runtime]

def reference (alpha0 alpha1 : L.E) (extra : Array L.K 2#usize) : Result (Array L.E 4#usize) := do
  let ap0 ← CuSavingsLibraCaller.powersCaller alpha0
  let ap1 ← CuSavingsLibraCaller.powersCaller alpha1
  CuSavingsLibraReferenceConcrete.reference ap0 ap1 extra

def optimized (alpha0 alpha1 : L.E) (extra : Array L.K 2#usize) : Result (Array L.E 4#usize) := do
  let ap0 ← CuSavingsLibraCaller.powersCaller alpha0
  let ap1 ← CuSavingsLibraCaller.powersCaller alpha1
  CuSavingsLibraCandidate14.optimized ap0 ap1 extra

/-- The source-entry witnesses are successful executions of the actual
sampler/semantic sampler or strict checkpoint reader. Canonicality is derived
here, not supplied as an extra field-validity or kernel-equivalence premise. -/
theorem source_equivalence (alpha0 alpha1 : L.E) (extra : Array L.K 2#usize)
    (ha0 : Alpha alpha0) (ha1 : Alpha alpha1)
    (hextra : ∀ i,i<2 → Extra (lookup extra AspisR1Libra.field.QM31.ONE i)) :
    optimized alpha0 alpha1 extra=reference alpha0 alpha1 extra := by
  obtain ⟨ap0,hp0,hv0⟩ := alpha_powers alpha0 ha0
  obtain ⟨ap1,hp1,hv1⟩ := alpha_powers alpha1 ha1
  simp only [optimized,reference,hp0,hp1,bind_tc_ok]
  exact CuSavingsLibraCandidate14.production_equivalence ap0 ap1 extra
    (fun i hi => (hv0 i hi).1) (fun i hi => (hv1 i hi).1)
    (fun i hi => extra_canonical _ (hextra i hi))

/-- The original low-array statement, inactive-row computation and suffix
are retained verbatim by the source inverse audit. This theorem composes
those computations around both exact helpers and their exact power builders.
Failure/divergence in any unchanged context is preserved. -/
theorem source_caller_context {T U : Type} (alpha0 alpha1 : L.E)
    (extra : Array L.K 2#usize) (ha0 : Alpha alpha0) (ha1 : Alpha alpha1)
    (hextra : ∀ i,i<2 → Extra (lookup extra AspisR1Libra.field.QM31.ONE i))
    (before : Array L.E 16#usize → Result T)
    (after : Array L.E 16#usize → T → Array L.E 4#usize → Result U) :
    (do
      let ap0 ← CuSavingsLibraCaller.powersCaller alpha0
      let ap1 ← CuSavingsLibraCaller.powersCaller alpha1
      let low ← CuSavingsLibraCaller.lowCaller ap0 ap1
      let common ← before low
      let result ← AspisR1Libra.new.factored_s2_libra_weights ap0 ap1 extra
      after low common result) =
    (do
      let ap0 ← CuSavingsLibraCaller.powersCaller alpha0
      let ap1 ← CuSavingsLibraCaller.powersCaller alpha1
      let low ← CuSavingsLibraCaller.lowCaller ap0 ap1
      let common ← before low
      let result ← AspisR1Libra.old.twofold_libra_weights low extra
      after low common result) := by
  obtain ⟨ap0,hp0,hv0⟩ := alpha_powers alpha0 ha0
  obtain ⟨ap1,hp1,hv1⟩ := alpha_powers alpha1 ha1
  simp only [hp0,hp1,bind_tc_ok]
  exact CuSavingsLibraCandidate14.caller_context ap0 ap1 extra
    (fun i hi => (hv0 i hi).1) (fun i hi => (hv1 i hi).1)
    (fun i hi => extra_canonical _ (hextra i hi)) before after

#print axioms source_equivalence
#print axioms source_caller_context
end AspisR1.CuSavingsLibraSourceOrigins
