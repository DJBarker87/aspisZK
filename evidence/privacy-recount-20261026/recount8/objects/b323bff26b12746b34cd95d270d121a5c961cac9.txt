import R1Z.PV_RunJoin_BatchRowValue44
import R1Z.PV_RunJoin_WideUnique44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BatchRowAssociation44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_BatchRowValue44 (table array)
variable [ExternalTypes]

theorem complete (ops : ExternalFuns) (c : Nat → Nat → Raw) (p : Nat → Raw)
    (hc : ∀ l, l < 29 → ∀ j, j < 1024 → canonical (c l j))
    (hp : ∀ l, l < 29 → canonical (p l)) (row : Usize) (hr : row.val < 1024) :
    ∃ z : Raw,
      @prover.opening_row _ (ProverRwP6BodyCandidate.selected ops) (table c) (array 29#usize p) row =
        .ok (current (source z)) ∧
      AspisR1ProducerRelease47.gamma53.cell (ProverCommitGammaCell53.table c) (sourceArray 29#usize p)
        row 0#usize 29#u8 AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO = .ok (source z) ∧
      canonical z ∧ value z = sum (fun l => c l row.val) p 29 0 := by
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitGammaCell53.exact_result c p hc hp row hr
  obtain ⟨y,hy,hcy,hdy⟩ := PV_RunJoin_BatchRowValue44.phase ops c p row hr
    (fun l hl => hc l hl row.val hr) hp 29 0#usize (by decide)
    ProverCommitGamma48.zero ProverCommitGamma48.zero_canonical
  have hdy0 : value y = sum (fun l => c l row.val) p 29 0 := by
    simpa only [ProverCommitGamma48.zero_value,zero_add,show (0#usize).val = 0 from rfl] using hdy
  have same : y = z := PV_RunJoin_WideUnique44.unique y z hcy hcz
    (hdy0.trans hdz.symm)
  subst y
  refine ⟨z,?_,hz,hcz,hdz⟩
  rw [@PV_RunJoin_BatchRowThread44.caller _ (ProverRwP6BodyCandidate.selected ops)]
  have zero : @aspis_core.field.wide_exact.WideExact.ZERO _ (ProverRwP6BodyCandidate.selected ops) =
      .ok (current (source ProverCommitGamma48.zero)) := by
    change Result.ok (current AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO) = _
    rw [ProverCommitGamma48.source_zero]
  rw [zero]
  simp only [bind_tc_ok]
  exact hy
#print axioms complete
end R1Z.PV_RunJoin_BatchRowAssociation44
