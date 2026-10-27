import XRk_PowersLoop
open Aeneas Aeneas.Std Result
open XRk_Release XRk_ResultTools
namespace XRk_PowersAssociation
/- Symbolic loop simulation: no concrete 29-step reduction or field-law premise. -/
theorem powers (gamma : aspis_core.field.wide_exact.WideExact)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (run : weights.powers 29#usize gamma = ok scratch) :
    ∃ one, aspis_core.field.wide_exact.WideExact.ONE = ok one ∧
      XRk_powers gamma 29 one = ok scratch.val := by
  unfold weights.powers at run
  obtain ⟨zero,_,run⟩ := bind_success _ _ _ run
  obtain ⟨one,hone,run⟩ := bind_success _ _ _ run
  obtain ⟨middle,pending,hloop,run⟩ := pair_bind_success _ _ _ run
  have selected : XRk_PowersLoop.chosen (middle,pending) = scratch := by
    cases pending <;> exact Result.ok.inj run
  obtain ⟨rest,href,hval⟩ := XRk_PowersLoop.suffix gamma
    (Array.repeat 29#usize zero) one 0#usize (middle,pending) (by decide) hloop
  change XRk_powers gamma 29 one = ok rest at href
  change (XRk_PowersLoop.chosen (middle,pending)).val = [] ++ rest at hval
  have same : rest = scratch.val := hval.symm.trans (congrArg Subtype.val selected)
  exact ⟨one,hone,href.trans (congrArg Result.ok same)⟩
#print axioms powers
end XRk_PowersAssociation
