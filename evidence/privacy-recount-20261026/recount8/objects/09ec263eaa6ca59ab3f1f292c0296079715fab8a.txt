import R1Z.PV_RunJoin_MergeArray35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_MergeStep35
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FieldData34 PV_RunJoin_MergeArray35
variable [ExternalTypes]

/-- Exact source stop, including the untouched accumulator. -/
theorem stop (ops : ExternalFuns)
    (e : Slice (core.result.Result Q r1_wire.Error)) (a count i : Usize)
    (p : Nat → Q) (hi : ¬ i<count) :
    @host_sumcheck.merge_evaluations_loop.body _ (ProverRwDictionaryTower.selected ops)
      e a count (array p) i = .ok (.done (array p,none)) := by
  simp only [host_sumcheck.merge_evaluations_loop.body,hi,if_false]

/-- First source error ends the sequential merge before any accumulator read
or division. Every failure class stays in the complete source Result. -/
theorem error (ops : ExternalFuns)
    (e : Slice (core.result.Result Q r1_wire.Error)) (a count i : Usize)
    (p : Nat → Q) (hi : i<count) (err : r1_wire.Error)
    (he : Slice.index_usize e i = .ok (.Err err)) :
    @host_sumcheck.merge_evaluations_loop.body _ (ProverRwDictionaryTower.selected ops)
      e a count (array p) i = .ok (.done (array p,some (.Err err))) := by
  simp only [host_sumcheck.merge_evaluations_loop.body,hi,if_true,he,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

/-- Actual source success step; the updated cell is the quotient-selected
sample, with exact canonical field addition and every other cell retained. -/
theorem success (ops : ExternalFuns)
    (e : Slice (core.result.Result Q r1_wire.Error)) (a count i : Usize)
    (p : Nat → Q) (hi : i<count) (positive : a.val≠0)
    (sample_bound : i.val/a.val<28) (v : Q)
    (he : Slice.index_usize e i = .ok (.Ok v))
    (hp : ∀ k, k<28 → canonical (p k)) (hv : canonical v) :
    ∃ sample : Usize, ∃ q : Q,
      sample.val=i.val/a.val ∧ canonical q ∧ value q=value (p sample.val)+value v ∧
      @host_sumcheck.merge_evaluations_loop.body _ (ProverRwDictionaryTower.selected ops)
        e a count (array p) i =
        .ok (.cont (array (Function.update p sample.val q),Usize.wrapping_add i 1#usize)) := by
  obtain ⟨sample,hs,hsv⟩ := UScalar.div_spec i (y := a) positive
  have hb : sample.val<28 := by rw [hsv];exact sample_bound
  obtain ⟨q,hq,hcq,hdq⟩ := PV_RunJoin_FieldData34.add ops (p sample.val) v (hp _ hb) hv
  refine ⟨sample,q,hsv,hcq,hdq,?_⟩
  simp only [host_sumcheck.merge_evaluations_loop.body,hi,if_true,he,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch,hs,read p sample hb,hq,
    write p sample hb q,lift]

#print axioms stop
#print axioms error
#print axioms success
end R1Z.PV_RunJoin_MergeStep35
