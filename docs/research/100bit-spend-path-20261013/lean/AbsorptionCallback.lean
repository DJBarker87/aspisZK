import AbsorptionGeneratedSlice
import ExtractedMaskQM31Exact
import R0P.Schedule

/-! Checked execution of the actual absorption callback. The exact source
association is retained in each of its three branches. -/
set_option autoImplicit false
namespace AspisR1.AbsorptionCallback
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskQM31Exact
abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Canonical := CurrentCanonicalQM
abbrev Closure := AspisR1AbsorptionCandidate.pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure
abbrev call := AspisR1AbsorptionCandidate.pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut

def blocksRun (fixed two eight nodes : QM) (lane : Usize) : Result QM :=
  if lane < 2#usize then .ok fixed
  else if lane < 8#usize then field.QM31.add fixed two
  else do
    let a ← field.QM31.add fixed two
    let b ← field.QM31.add a eight
    field.QM31.add b nodes

def blocksModel (fixed two eight nodes : ExactQM) (lane : Nat) : ExactQM :=
  if lane < 2 then fixed else if lane < 8 then fixed + two else ((fixed + two) + eight) + nodes

theorem blocks_success (fixed two eight nodes : QM) (lane : Usize)
    (hf : Canonical fixed) (ht : Canonical two) (he : Canonical eight) (hn : Canonical nodes) :
    ∃ out, blocksRun fixed two eight nodes lane = .ok out ∧ Canonical out ∧
      decode out = blocksModel (decode fixed) (decode two) (decode eight) (decode nodes) lane.val := by
  have h2 : (2#usize).val = 2 := by scalar_tac
  have h8 : (8#usize).val = 8 := by scalar_tac
  by_cases hsmall : lane.val < 2
  · refine ⟨fixed, ?_, hf, ?_⟩
    · simp only [blocksRun, UScalar.lt_equiv, h2, hsmall, if_true]
    · simp only [blocksModel, hsmall, if_true]
  · obtain ⟨a, ha, hca, hva⟩ := current_qm_add_exact fixed two hf ht
    by_cases hmid : lane.val < 8
    · refine ⟨a, ?_, hca, ?_⟩
      · simp only [blocksRun, UScalar.lt_equiv, h2, h8, hsmall, hmid, if_false, if_true, ha]
      · simpa only [blocksModel, hsmall, hmid, if_false, if_true] using hva
    · obtain ⟨b, hb, hcb, hvb⟩ := current_qm_add_exact a eight hca he
      obtain ⟨out, ho, hco, hvo⟩ := current_qm_add_exact b nodes hcb hn
      refine ⟨out, ?_, hco, ?_⟩
      · simp only [blocksRun, UScalar.lt_equiv, h2, h8, hsmall, hmid, if_false, ha, bind_tc_ok, hb, ho]
      · rw [hvo, hvb, hva]
        simp only [blocksModel, hsmall, hmid, if_false]

private theorem index_success {N : Usize} (a : Array QM N) (i : Usize)
    (hi : i.val < N.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hb : i.val < a.length := by simpa [a.property] using hi
  obtain ⟨q, hread, hvalue⟩ := WP.spec_imp_exists (Array.index_usize_spec a i hb)
  rw [hread]
  congr 1

private theorem bind_if {α β : Type} (p : Prop) [Decidable p]
    (a b : Result α) (f : α → Result β) :
    ((if p then a else b) >>= f) = (if p then a >>= f else b >>= f) := by
  split_ifs <;> rfl

def sourceCell (a : Array QM 16#usize) (i : Fin 16) : QM :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)

theorem callback_success (low fixed two eight nodes : QM)
    (openings : Array QM 16#usize) (lane : Usize) (hlane : lane.val < 16)
    (hl : Canonical low) (hf : Canonical fixed) (ht : Canonical two)
    (he : Canonical eight) (hn : Canonical nodes)
    (ho : ∀ i : Fin 16, Canonical (sourceCell openings i)) :
    ∃ out, call (fixed, two, eight, nodes, low, openings) lane =
        .ok (out, (fixed, two, eight, nodes, low, openings)) ∧ Canonical out ∧
      decode out = decode low *
        blocksModel (decode fixed) (decode two) (decode eight) (decode nodes) lane.val *
        decode (sourceCell openings ⟨lane.val, hlane⟩) := by
  obtain ⟨blocks, hb, hcb, hvb⟩ := blocks_success fixed two eight nodes lane hf ht he hn
  obtain ⟨scale, hs, hcs, hvs⟩ := current_qm_mul_exact low blocks hl hcb
  let cell := sourceCell openings ⟨lane.val, hlane⟩
  have hread : Array.index_usize openings lane = .ok cell :=
    index_success openings lane (by simpa using hlane)
  have hc : Canonical cell := ho ⟨lane.val, hlane⟩
  obtain ⟨out, hout, hco, hvo⟩ := current_qm_mul_exact scale cell hcs hc
  refine ⟨out, ?_, hco, ?_⟩
  · have hbind := congrArg (fun r : Result QM => do
      let b ← r
      let s ← field.QM31.mul low b
      let x ← Array.index_usize openings lane
      let y ← field.QM31.mul s x
      .ok (y, (fixed, two, eight, nodes, low, openings))) hb
    simp only [blocksRun, bind_if, bind_assoc, bind_tc_ok, hs, hread, hout] at hbind
    simpa only [call,
      AspisR1AbsorptionCandidate.pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut,
      AspisR1AbsorptionCandidate.poseidon2.RATE,
      AspisR1AbsorptionCandidate.pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure,
      bind_tc_ok, hs, hread, hout] using hbind
  · rw [hvo, hvs, hvb]

#print axioms blocks_success
#print axioms callback_success
end
end AspisR1.AbsorptionCallback
