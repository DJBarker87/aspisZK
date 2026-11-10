import NJU_FieldScalar

/-! NPH_ (R22 item 2, AspisR1WeightsFieldCurrent.weights.field): the index domain at its call sites.
weights.field's checked operations i * 32, i + 1 and (i + 1) * 32 are ok with their exact values
for i < 64 (NJU_FieldScalar.checked). This module states that domain at every located site:
- the literal sites: finish_relation_round reads 0 and 4, the Horner polynomial
  (FIn_Polynomial.polynomial) and FIn_ExtractFuns read 6, 5, ..., 0 (`literal_sites`);
- the finish dot finish_query_dot_loop.body reads j under its guard j < len weights, so the
  domain holds whenever len weights <= 64 (`dot_site`);
- the claim dot (CurrentClaimDotModel, ClaimParser.field) reads l, so the domain holds whenever
  l < 64 (`claim_site`).
Not composed here (the residual): len weights <= 64 at the deployed tx2 finish call (weights is
the op9 flush of the op6 query-loop accumulator; FIn_WeightLength.twelve states 64 on the
Cons_NativeBuild witness of an accepted run, NFS_QueryInvariant.Domain.width states 64 at every
reached query state), and the claim-dot iterator bound l < 64. Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22FieldSites
open Aeneas Aeneas.Std Result

abbrev Ok3 (i : Usize) : Prop :=
  (∃ a, (i * 32#usize : Result Usize) = ok a ∧ a.val = i.val * 32) ∧
  (∃ n, (i + 1#usize : Result Usize) = ok n ∧ n.val = i.val + 1 ∧
    ∃ b, (n * 32#usize : Result Usize) = ok b ∧ b.val = (i.val + 1) * 32)

theorem domain_ok (i : Usize) (small : i.val < 64) : Ok3 i := by
  obtain ⟨m0, a1, m1⟩ := NJU_FieldScalar.checked i small
  refine ⟨⟨_, m0, ?_⟩, ⟨_, a1, ?_, _, m1, ?_⟩⟩
  · simp only [NJU_FieldScalar.start]; first | rfl | simp | scalar_tac
  · simp only [NJU_FieldScalar.next]; first | rfl | simp | scalar_tac
  · simp only [NJU_FieldScalar.stop]; first | rfl | simp | scalar_tac

theorem literal_sites :
    Ok3 0#usize ∧ Ok3 1#usize ∧ Ok3 2#usize ∧ Ok3 3#usize ∧ Ok3 4#usize ∧ Ok3 5#usize ∧ Ok3 6#usize :=
  ⟨domain_ok _ (by decide), domain_ok _ (by decide), domain_ok _ (by decide), domain_ok _ (by decide),
    domain_ok _ (by decide), domain_ok _ (by decide), domain_ok _ (by decide)⟩

theorem dot_site {T : Type} (weights : Slice T) (j : Usize) (guard : j < Slice.len weights)
    (width : weights.val.length ≤ 64) : Ok3 j := by
  have hl : (Slice.len weights).val = weights.val.length := by
    first | rfl | simp [Slice.len_val] | simp [Slice.len] | scalar_tac
  have hj : j.val < (Slice.len weights).val := guard
  exact domain_ok j (by omega)

theorem claim_site (l : Usize) (hl : l.val < 64) : Ok3 l := domain_ok l hl

#print axioms domain_ok
#print axioms literal_sites
#print axioms dot_site
#print axioms claim_site
end AspisR1.NPH_R22FieldSites
