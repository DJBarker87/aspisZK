import DotPushSourceResidues
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1DotPushLocal.Proof

theorem push_success_raw_and_state
    (rawFn : canonical.Q → canonical.Q → Result (Array U64 4#usize))
    (self : canonical.Dot) (left right : canonical.Q) (out : canonical.Dot)
    (hrun : canonical.Dot.push rawFn self left right = .ok out) :
    ∃ raw : Array U64 4#usize,
      rawFn left right = .ok raw ∧ out.sums=updatedSums self.sums raw := by
  cases hr : rawFn left right with
  | ok raw =>
      have htotal := push_total_from_raw rawFn self left right raw hr
      have he : out=⟨updatedSums self.sums raw⟩ := Result.ok.inj (hrun.symm.trans htotal)
      exact ⟨raw,hr,congrArg canonical.Dot.sums he⟩
  | fail e => simp only [canonical.Dot.push,hr,bind_tc_fail] at hrun;cases hrun
  | div => simp only [canonical.Dot.push,hr,bind_tc_div] at hrun;cases hrun

theorem push_success_residues
    (rawFn : canonical.Q → canonical.Q → Result (Array U64 4#usize))
    (self : canonical.Dot) (left right : canonical.Q) (out : canonical.Dot)
    (hrun : canonical.Dot.push rawFn self left right = .ok out)
    (hbound : ∀ x ∈ self.sums.val, x.val < 2 ^ 46) :
    ∃ raw : Array U64 4#usize,
      rawFn left right = .ok raw ∧ out.sums=updatedSums self.sums raw ∧
      ∀ j : Nat, ∀ hj : j<4,
        (out.sums.val[j]'(by rw [out.sums.property];exact hj)).val % AspisR1EbyKDotPushNatStep.modulus =
          ((self.sums.val[j]'(by rw [self.sums.property];exact hj)).val +
           (raw.val[j]'(by rw [raw.property];exact hj)).val) % AspisR1EbyKDotPushNatStep.modulus := by
  obtain ⟨raw,hraw,hstate⟩ := push_success_raw_and_state rawFn self left right out hrun
  refine ⟨raw,hraw,hstate,?_⟩
  intro j hj
  rw [hstate]
  exact updatedSums_residue self.sums raw hbound j hj

#print axioms push_success_raw_and_state
#print axioms push_success_residues
end AspisR1DotPushLocal.Proof
