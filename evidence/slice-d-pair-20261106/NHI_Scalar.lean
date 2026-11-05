import NHI_ScalarFold
import NHE_ScalePort
set_option autoImplicit false
namespace NHI_Scalar
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
abbrev zero := FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO

def reference (f : Array NQ 4#usize) (p : Array NE 4#usize) : Result NE := do
 let sum ← NHI_ScalarFold.cells p f 4 0#usize zero
 FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 sum FIo_Native.weights.QUARTER

theorem zero_canonical : canonE zero := by
 unfold zero FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
 unfold FIo_Native.aspis_core.field.QM31.ZERO
 simp only [canonE,canonQ,canonC,LPi_CMProduct.Canon]
 decide

theorem four (p : Array NE 4#usize) (f : Array NQ 4#usize)
 (hp : ∀ x∈p.val,canonE x) (hf : ∀ x∈f.val,canonQ x) :
 ∃ sum,FIo_Native.core.iter.traits.iterator.Iterator.fold.default NHI_ScalarFold.iterator NHI_ScalarFold.fnmut
 {start:=0#usize,«end»:=4#usize} zero (p,f)=ok sum ∧
 NHI_ScalarFold.cells p f 4 0#usize zero=ok sum ∧ canonE sum := by
 obtain ⟨sum,run,ref,co⟩ := NHI_ScalarFold.finite p f hp hf 4
  {start:=0#usize,«end»:=4#usize} rfl rfl zero zero_canonical
 exact ⟨sum,run,ref,co⟩

/-- The exact source fold/quarter Result on the canonical SAME-array domain.
All per-cell products are discharged by NHE_ScalarProductLaw.product; the
terminal scale is discharged by NGM_RoundScale.total. -/
theorem cohort (f : Array NQ 4#usize) (p : Array NE 4#usize)
 (hp : ∀ x∈p.val,canonE x) (hf : ∀ x∈f.val,canonQ x) :
 FIo_Native.weights.Weights.scalar_factor f p=reference f p := by
 obtain ⟨sum,run,ref,co⟩ := four p f hp hf
 unfold FIo_Native.weights.Weights.scalar_factor reference
 rw [run,ref]

theorem total (f : Array NQ 4#usize) (p : Array NE 4#usize)
 (hp : ∀ x∈p.val,canonE x) (hf : ∀ x∈f.val,canonQ x) :
 ∃ sum out, NHI_ScalarFold.cells p f 4 0#usize zero=ok sum ∧ canonE sum ∧
 FIo_Native.weights.Weights.scalar_factor f p=ok out ∧ canonE out ∧
 NGM_RoundScale.limbs out=(NGM_RoundScale.limbs sum).map (fun word=>(word*536870912)%2147483647) := by
 obtain ⟨sum,run,ref,co⟩ := four p f hp hf
 obtain ⟨out,scale,canonical,values⟩ := NGM_RoundScale.total sum
 refine ⟨sum,out,ref,co,?_,canonical,values⟩
 unfold FIo_Native.weights.Weights.scalar_factor
 rw [run,bind_tc_ok]
 simpa only [FIo_Native.weights.QUARTER] using scale

#print axioms zero_canonical
#print axioms four
#print axioms cohort
#print axioms total
end NHI_Scalar
