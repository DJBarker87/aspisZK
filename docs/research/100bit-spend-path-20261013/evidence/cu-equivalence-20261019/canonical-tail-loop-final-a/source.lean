import CuSavingsCanonicalTailStep
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
namespace AspisR1.CuSavingsCanonicalTailLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1CanonicalDots
open CuSavingsCanonicalDotsPush CuSavingsCanonicalDotsField
open CuSavingsCanonicalVectorLoop CuSavingsCanonicalTailStep OccupancyRangeTraversal
variable [Shared] [VectorCommon]


theorem execute_unroll {S V O : Type} (body : S→Result (ControlFlow S V)) (state : S)
    (k : V→Result O) :
    (do let value←loop body state;k value) = (do
      let step←body state
      match step with
      | .cont next => do let value←loop body next;k value
      | .done value => k value) := by
  rw [loop]
  cases hs : body state with
  | fail e => rfl
  | div => rfl
  | ok step => cases step <;> rfl

theorem source_transport {O : Type} (fuel : Nat)
    (newK : new_pairing.EbyKDot→Result O) (oldK : old_pairing.EbyKDot→Result O)
    (hk : ∀ state,RelatedCounts state→newK (project state)=oldK state)
    (iter : Range) (q : Slice U8) (g : G) (hg : CanonicalG g) (slot : Usize)
    (dot : old_pairing.EbyKDot) (hc : RelatedCounts dot)
    (he : iter.end.val=2) (hi : iter.start.val≤2) (hf:2-iter.start.val=fuel) :
    (do let state←new_callers.tail_loop iter q g slot (project dot);newK state) =
      (do let state←old_callers.tail_loop iter q g slot dot;oldK state) := by
  induction fuel generalizing iter dot with
  | zero =>
      have hn := next_done iter (by omega)
      unfold new_callers.tail_loop old_callers.tail_loop
      rw [loop,loop]
      simp only [new_callers.tail_loop.body,old_callers.tail_loop.body,
        hn,bind_tc_ok,uncurry_apply_pair]
      exact hk dot hc
  | succ fuel ih =>
      obtain ⟨next,hn,hinc,hend,_⟩ := next_step iter (by omega)
      unfold new_callers.tail_loop old_callers.tail_loop
      rw [execute_unroll,execute_unroll]
      dsimp only
      simp only [new_callers.tail_loop.body,old_callers.tail_loop.body,
        hn,bind_tc_ok,uncurry_apply_pair,bind_assoc_eq]
      apply (bind_eq_iff _ _ _).mpr
      intro i0 _
      apply (bind_eq_iff _ _ _).mpr
      intro i1 _
      apply (bind_eq_iff _ _ _).mpr
      intro i2 _
      apply (bind_eq_iff _ _ _).mpr
      intro i3 _
      apply (bind_eq_iff _ _ _).mpr
      intro i4 _
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
      rw [public_push dot value a3 hv hc]
      simp only [bind_assoc_eq,bind_tc_ok,uncurry_apply_pair]
      cases hp : old_pairing.EbyKDot.push dot value a3 with
      | fail error => rfl
      | div => rfl
      | ok pair =>
        rcases pair with ⟨result,after⟩
        cases result with
        | Err error => rfl
        | Ok unit =>
          exact ih next after
            (CuSavingsCanonicalDotsInvariant.push_counts dot after value a3 hv hc hp)
            (by rw [hend];exact he) (by omega) (by omega)

#print axioms execute_unroll
#print axioms source_transport
end AspisR1.CuSavingsCanonicalTailLoop
