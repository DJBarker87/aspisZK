import LPi_PowersSource
set_option autoImplicit false
namespace AspisR1.LPi_PowersWitness
open Aeneas Aeneas.Std Result LPi_FieldValues LPi_PowersPrefix

/-- Every canonical challenge has a successful powers7 result with nonzero
first entry. This is a source-domain witness, not joint headline non-vacuity. -/
theorem first_limb (x : NE) (hx : canonE x) : ∃ out z,
    FIo_Native.weights.powers 7#usize x=ok out ∧ out.val[0]?=some z ∧
      canonE z ∧ z.c0.c0.a.val=1 := by
  obtain ⟨out,run,hold⟩ := LPi_PowersSource.seven x hx
  obtain ⟨z,index,canonical,value⟩ := hold 0 (by decide)
  change ew z=ew FIo_Native.aspis_core.field.wide_exact.WideExact.ONE at value
  have v := congrArg (fun w : EW => w.1.1.1) value
  have one : (ew FIo_Native.aspis_core.field.wide_exact.WideExact.ONE).1.1.1=1 := by
    simp only [ew,qw,cw,FIo_Native.aspis_core.field.wide_exact.WideExact.ONE,
      FIo_Native.aspis_core.field.QM31.ONE]
  exact ⟨out,z,run,index,canonical,v.trans one⟩

theorem inhabited : ∃ out, FIo_Native.weights.powers 7#usize
    FIo_Native.aspis_core.field.wide_exact.WideExact.ONE=ok out := by
  obtain ⟨out,run,_⟩ := LPi_PowersSource.seven _ LPi_PowersSource.one_canonical
  exact ⟨out,run⟩

#print axioms first_limb
#print axioms inhabited
end AspisR1.LPi_PowersWitness
