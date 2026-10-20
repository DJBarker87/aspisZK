import FinishCandidateEquations
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FinishRoundAlphaSemantic
open _root_.AspisR1FinishRelationCurrent

private theorem array_index_usize_ok {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

theorem alpha_at_zero (p : verifier.Prepared) (x : aspis_core.field.WideExact)
    (h : Array.index_usize p.alpha 0#usize = .ok x) :
    x = p.alpha.val[0]'(by
      have hlen : (0#usize).val < (2#usize).val := by scalar_tac
      simpa [p.alpha.property] using hlen) := by
  have hlen : (0#usize).val < (2#usize).val := by scalar_tac
  have hread := array_index_usize_ok p.alpha 0#usize hlen
  simpa using (Result.ok.inj (h.symm.trans hread))

theorem alpha_at_one (p : verifier.Prepared) (x : aspis_core.field.WideExact)
    (h : Array.index_usize p.alpha 1#usize = .ok x) :
    x = p.alpha.val[1]'(by
      have hlen : (1#usize).val < (2#usize).val := by scalar_tac
      simpa [p.alpha.property] using hlen) := by
  have hlen : (1#usize).val < (2#usize).val := by scalar_tac
  have hread := array_index_usize_ok p.alpha 1#usize hlen
  simpa using (Result.ok.inj (h.symm.trans hread))

#print axioms alpha_at_zero
#print axioms alpha_at_one
end AspisR1FinishRoundAlphaSemantic
