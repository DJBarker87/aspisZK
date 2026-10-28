import R1Z.PV_RunJoin_RoundFibreValue44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundAccumulation44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48 ProverCommitRoundLoop48
open PV_RunJoin_WideArithmetic44
open PV_RunJoin_FoldCell44 (array)
variable [ExternalTypes]

theorem complete (ops : ExternalFuns) (count : Usize) (small : count.val / 4 ≤ 256)
    (q w : Nat → Raw) (hq : ∀ k, k < 1024 → canonical (q k))
    (hw : ∀ k, k < 1024 → canonical (w k)) :
    ∃ ys : Nat → Raw,
      @prover.round_loop0 _ (ProverRwP6BodyCandidate.selected ops)
        (Array.to_slice (array count q)) (Array.to_slice (array count w))
        (Array.repeat 7#usize (current AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO)) 0#usize =
          .ok (array 7#usize ys) ∧
      (∀ k, k < 7 → canonical (ys k)) ∧
      ∀ k, k < 7 → value (ys k) = terms q w (ProverCommitRoundOutput48.indices (count.val / 4)) k := by
  obtain ⟨ys,hy,hcy,hdy⟩ := PV_RunJoin_RoundFibreValue44.complete ops count q w
    (fun _ => ProverCommitGamma48.zero) hq hw (fun _ _ => ProverCommitGamma48.zero_canonical)
    0#usize (count.val / 4) (by change 0 + _ = _;omega) small
  refine ⟨ys,?_,hcy,?_⟩
  · have init : Array.repeat 7#usize (current AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO) =
        array 7#usize (fun _ => ProverCommitGamma48.zero) := by
      rw [ProverCommitGamma48.source_zero]
      apply Subtype.ext
      simp only [Array.repeat,array,ProverCommitArray49.array,List.ofFn_const]
    rw [init,@PV_RunJoin_RoundFibreThread44.complete _ (ProverRwP6BodyCandidate.selected ops)
      _ _ _ 0#usize (count.val / 4)
      (by rw [Array.length_to_slice];change 0 + _ = _;omega)
      (by rw [Array.length_to_slice];exact small)]
    exact hy
  · intro k hk
    simpa only [ProverCommitGamma48.zero_value,zero_add,PV_RunJoin_RoundTerms44.indices] using hdy k hk
#print axioms complete
end R1Z.PV_RunJoin_RoundAccumulation44
