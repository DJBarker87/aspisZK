import NGO_PrefixWidePort
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace NGO_PrefixLimbsLaw
open NGO_PrefixWidePort
def atWord (w : Array U32 8#usize) (i : Fin 8) : U32 :=
  w.val[i.val]'(by rw [w.property];exact i.isLt)
def assembled (w : Array U32 8#usize) : WireWide :=
  ⟨⟨⟨atWord w 0,atWord w 1⟩,⟨atWord w 2,atWord w 3⟩⟩,
   ⟨⟨atWord w 4,atWord w 5⟩,⟨atWord w 6,atWord w 7⟩⟩⟩
noncomputable def expected (w : Array U32 8#usize) : Option WireWide :=
  if ∀ i : Fin 8, (atWord w i).val<2147483647 then some (assembled w) else none
/-- Exact canonicality checks and raw tower on all eight arbitrary words. -/
theorem result (w : Array U32 8#usize) :
    AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_limbs w=ok (expected w) := by
  have spec : AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_limbs w ⦃ out=>out=expected w ⦄ := by
    unfold AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_limbs
    step*
    all_goals simp_all [expected,assembled,atWord,Fin.forall_fin_succ,
      AspisR1PrefixAggregateParser.field.P]
  obtain ⟨out,run,eq⟩ := WP.spec_imp_exists spec
  exact run.trans (congrArg ok eq)
#print axioms result
end NGO_PrefixLimbsLaw
