import CuSavingsCanonicalTailLoop
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
namespace AspisR1.CuSavingsCanonicalTail
open Aeneas Aeneas.Std Result AspisR1CanonicalDots
open CuSavingsCanonicalDotsPush CuSavingsCanonicalDotsField
open CuSavingsCanonicalVectorLoop CuSavingsCanonicalTailStep
variable [Shared] [VectorCommon]

theorem source_eq (q : Slice U8) (g : G) (hg : CanonicalG g) (slot : Usize) :
    new_callers.tail q g slot=old_callers.tail q g slot := by
  simp only [new_callers.tail,old_callers.tail,
    CuSavingsCanonicalDotsInvariant.old_new,CuSavingsCanonicalDotsInvariant.new_new,bind_tc_ok]
  apply (bind_eq_iff _ _ _).mpr
  intro value hread
  have hv := read_canonical g hg _ value hread
  apply (bind_eq_iff _ _ _).mpr
  intro a0 _
  apply (bind_eq_iff _ _ _).mpr
  intro a1 _
  apply (bind_eq_iff _ _ _).mpr
  intro a2 _
  apply (bind_eq_iff _ _ _).mpr
  intro a3 _
  apply (bind_eq_iff _ _ _).mpr
  intro a4 _
  apply (bind_eq_iff _ _ _).mpr
  intro scalar _
  rw [public_push CuSavingsCanonicalDotsInvariant.initial value scalar hv
    CuSavingsCanonicalDotsInvariant.initial_counts]
  simp only [bind_assoc_eq,bind_tc_ok,uncurry_apply_pair]
  cases hp : old_pairing.EbyKDot.push CuSavingsCanonicalDotsInvariant.initial value scalar with
  | fail error => rfl
  | div => rfl
  | ok pair =>
    rcases pair with ⟨result,after⟩
    cases result with
    | Err error => rfl
    | Ok unit =>
      have hcounts := CuSavingsCanonicalDotsInvariant.push_counts
        CuSavingsCanonicalDotsInvariant.initial after value scalar hv
        CuSavingsCanonicalDotsInvariant.initial_counts hp
      exact CuSavingsCanonicalTailLoop.source_transport 2
        new_pairing.EbyKDot.finish old_pairing.EbyKDot.finish
        (fun state _ => CuSavingsCanonicalCandidate5.finalization state)
        {start:=0#usize,«end»:=2#usize} q g hg slot after hcounts
        (by scalar_tac) (by scalar_tac) (by scalar_tac)

theorem from_powers [AspisR1CanonicalSampler.Shared] [AspisR1CanonicalReader.Runtime]
    (q : Slice U8) (slot : Usize)
    (base : CuSavingsCanonicalDotsSources.I) (hb : CuSavingsCanonicalDotsSources.SourceValue base)
    (values : Array CuSavingsCanonicalDotsSources.I 29#usize)
    (h : AspisR1CanonicalInputs.weights.powers 29#usize base=.ok values) :
    new_callers.tail q (dotTable values) slot=old_callers.tail q (dotTable values) slot := by
  apply source_eq
  intro i hi
  have hlen : values.val.length=(29#usize).val := values.property
  have hbnd : i<(29#usize).val := by simpa only [dotTable,List.length_map,hlen] using hi
  obtain ⟨out,hr,hc⟩ := CuSavingsCanonicalInputPowers.source_success 29#usize base
    (CuSavingsCanonicalDotsSources.source_canonical base hb)
  have heq := Result.ok.inj (hr.symm.trans h)
  cases heq
  simp only [dotTable,List.getElem_map]
  exact CuSavingsCanonicalDotsSources.input_canonical _ (hc i hbnd).1

#print axioms source_eq
#print axioms from_powers
end AspisR1.CuSavingsCanonicalTail
