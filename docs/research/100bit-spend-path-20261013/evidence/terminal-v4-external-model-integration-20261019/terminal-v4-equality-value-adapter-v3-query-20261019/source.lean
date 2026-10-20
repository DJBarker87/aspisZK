import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
import TerminalV4TerminalPartsChunk08V2
import TerminalV4QM31ExactV5
import TerminalV4ConstantsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace AspisR1.TerminalV4EqualityValueAdapter
open Aeneas.Std Result

abbrev QM := AspisR1.TerminalV4QM31Exact.CurrentQM
abbrev ExactQM := AspisR1.TerminalV4QM31Exact.QM31Exact
abbrev Canonical := AspisR1.TerminalV4QM31Exact.CurrentCanonicalQM

def decode (x : QM) : ExactQM := AspisR1.TerminalV4QM31Exact.decode x

def factor (a b : ExactQM) : ExactQM := 1 - a - b + a * b + a * b

/-- The extracted closure's algebraic factor, with each current operation
kept explicit in the success result and canonicality chain. -/
theorem equality_factor_call (a b : QM)
    (ha : Canonical a) (hb : Canonical b) :
    ∃ z,
      AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.equality_value.closure.Insts.CoreOpsFunctionFnPairQM31QM31QM31.call
        () (a, b) = .ok z ∧
      Canonical z ∧ decode z = factor (decode a) (decode b) := by
  obtain ⟨ab, hab, habcan, habval⟩ :=
    AspisR1.TerminalV4QM31Exact.current_qm_mul_exact a b ha hb
  obtain ⟨q, hq, hqcan, hqval⟩ :=
    AspisR1.TerminalV4QM31Exact.current_qm_sub_exact AspisR1SelectedMaskProbe.field.QM31.ONE a
      (AspisR1.TerminalV4Constants.one_canonical) ha
  obtain ⟨q1, hq1, hq1can, hq1val⟩ := AspisR1.TerminalV4QM31Exact.current_qm_sub_exact q b hqcan hb
  obtain ⟨q2, hq2, hq2can, hq2val⟩ :=
    AspisR1.TerminalV4QM31Exact.current_qm_add_exact q1 ab hq1can habcan
  obtain ⟨q3, hq3, hq3can, hq3val⟩ :=
    AspisR1.TerminalV4QM31Exact.current_qm_add_exact q2 ab hq2can habcan
  have hqval' : AspisR1.TerminalV4QM31Exact.decode q =
      AspisR1.TerminalV4QM31Exact.decode AspisR1SelectedMaskProbe.field.QM31.ONE -
        AspisR1.TerminalV4QM31Exact.decode a := by
    exact hqval
  have hq1val' : AspisR1.TerminalV4QM31Exact.decode q1 =
      AspisR1.TerminalV4QM31Exact.decode q -
        AspisR1.TerminalV4QM31Exact.decode b := by
    exact hq1val
  refine ⟨q3, ?_, hq3can, ?_⟩
  · unfold AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.equality_value.closure.Insts.CoreOpsFunctionFnPairQM31QM31QM31.call
    simp only [hab, hq, hq1, hq2, hq3, bind_tc_ok]
  · change decode q3 = factor (decode a) (decode b)
    dsimp [factor]
    change AspisR1.TerminalV4QM31Exact.decode q3 =
      1 - AspisR1.TerminalV4QM31Exact.decode a -
        AspisR1.TerminalV4QM31Exact.decode b +
        AspisR1.TerminalV4QM31Exact.decode a *
          AspisR1.TerminalV4QM31Exact.decode b +
        AspisR1.TerminalV4QM31Exact.decode a *
          AspisR1.TerminalV4QM31Exact.decode b
    rw [hq3val, hq2val, hq1val', hqval', habval,
      AspisR1.TerminalV4Constants.one_decode]


#print axioms equality_factor_call

end AspisR1.TerminalV4EqualityValueAdapter
