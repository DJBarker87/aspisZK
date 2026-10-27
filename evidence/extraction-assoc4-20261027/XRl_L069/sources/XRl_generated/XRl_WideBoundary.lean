import XRk_PushTrace
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal
namespace XRl_WideBoundary
/-- The extracted carrier has no private-constructor invariant. This value
cannot arise from the native canonical WideExact constructor. -/
def invalidWide : XRk_Wide :=
  ⟨oldQ ⟨⟨2147483647#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,oldQ qzero⟩
def initial : fast_pairing.EbyKDot := ⟨XRk_dotZero,XRk_dotZero,0#usize⟩

theorem invalid_coordinate :
    ¬ XRk_CanonicalScalar.Canonical (newQ invalidWide.c0) := by
  intro h
  have bad := h.1
  change (2147483647#u32).val < (2147483647#u32).val at bad
  exact Nat.lt_irrefl _ bad

/-- Actual modeled from_wide accepts this carrier unchanged. This refutes
canonicality from carrier typing alone, without any expensive dot reduction. -/
theorem unchecked_wide_projection :
    fast_pairing.canonical.Q.from_wide invalidWide =
      ok (Array.make 2#usize [
        Array.make 4#usize [2147483647#u32,0#u32,0#u32,0#u32],
        Array.make 4#usize [0#u32,0#u32,0#u32,0#u32]]) := by rfl

/-- One reached accepted push is not enough to recover the native type's
private canonical-operand invariant from this unrefined extracted carrier.
Only one four-cell modeled push reduces here, no long recurrence. -/
theorem invalid_wide_accepted :
    ∃ next, fast_pairing.EbyKDot.push initial invalidWide qzero=ok (.Ok (),next) := by
  unfold fast_pairing.EbyKDot.push fast_pairing.MAX_TERMS
  have below : ¬initial.count ≥ 4096#usize := by
    change ¬(0#usize) ≥ 4096#usize
    scalar_tac
  rw [if_neg below]
  simp only [fast_pairing.canonical.Dot.push,List.length_map,List.length_range,↓reduceDIte]
  have checked : fast_pairing.checked_q qzero=ok (.Ok (XRk_toQ qzero)) := by
    unfold fast_pairing.checked_q fast_pairing.limbs_of fast_pairing.canonical.Q.from_limbs fast_pairing.canonical.P
    rfl
  simp only [checked,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  have plus : initial.count+1#usize=ok 1#usize := by
    change (0#usize)+1#usize=ok 1#usize
    scalar_tac
  simp only [plus,bind_tc_ok]
  exact ⟨_,rfl⟩
#print axioms invalid_wide_accepted
#print axioms invalid_coordinate
#print axioms unchecked_wide_projection
end XRl_WideBoundary
