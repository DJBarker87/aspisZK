import CuSavingsRetainedFinishBinding
import CuSavingsRhoEntryTransport
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedFinishTransport
open Aeneas Aeneas.Std Result
open CuSavingsLibraConcrete CuSavingsRetainedCompositionWeightsInputs
variable [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalKReader.Runtime] [AspisR1S2Groups.Shared]
theorem scalar_canonical (q : P.K) (hc : canonicalK (libraK q)) :
    CuSavingsRhoInitRow.Canonical (CuSavingsRhoEntryTransport.scalar q) := by
  intro i
  fin_cases i <;> first | exact hc.1.1 | exact hc.1.2 | exact hc.2.1 | exact hc.2.2

theorem inputs (p : P.Prepared)
    (ha : ∃ a0 a1,p.alpha=Array.make 2#usize [a0,a1] ∧
      CuSavingsLibraOrigins.Alpha (CuSavingsRetainedSamplerBinding.libra a0) ∧
      CuSavingsLibraOrigins.Alpha (CuSavingsRetainedSamplerBinding.libra a1))
    (hc : ∀ i : Fin 10,canonicalK (libraK (semanticAt p.semantic_alpha i))) :
    (∃ a0 a1,(CuSavingsRhoEntryTransport.prepared p).alpha=Array.make 2#usize [a0,a1] ∧
      CuSavingsLibraOrigins.Alpha (CuSavingsRetainedResumeOrigins.libra a0) ∧
      CuSavingsLibraOrigins.Alpha (CuSavingsRetainedResumeOrigins.libra a1)) ∧
    (∀ (i : Nat) (hi : i<(CuSavingsRhoEntryTransport.prepared p).semantic_alpha.val.length),
      CuSavingsRhoInitRow.Canonical ((CuSavingsRhoEntryTransport.prepared p).semantic_alpha.val[i]'hi)) := by
  constructor
  · obtain ⟨a0,a1,ha,h0,h1⟩:=ha
    refine ⟨CuSavingsRhoEntryTransport.wide a0,CuSavingsRhoEntryTransport.wide a1,?_,h0,h1⟩
    change CuSavingsRhoEntryTransport.array CuSavingsRhoEntryTransport.wide p.alpha=_
    rw [ha]
    rfl
  · intro i hi
    have hip : i<p.semantic_alpha.val.length := by simpa only [CuSavingsRhoEntryTransport.prepared,CuSavingsRhoEntryTransport.array,List.length_map] using hi
    have hi10 : i<10 := by rw [p.semantic_alpha.property] at hip;exact hip
    change CuSavingsRhoInitRow.Canonical ((p.semantic_alpha.val.map CuSavingsRhoEntryTransport.scalar)[i]'_)
    rw [List.getElem_map]
    exact scalar_canonical _ (hc ⟨i,hi10⟩)

#print axioms inputs
end AspisR1.CuSavingsRetainedFinishTransport
