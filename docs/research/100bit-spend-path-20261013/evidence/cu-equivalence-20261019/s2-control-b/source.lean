import AspisR1S2Groups.Funs
import Mathlib.Tactic.IntervalCases
import CuSavingsS2TableData
import OccupancyRangeTraversal
set_option autoImplicit false
namespace AspisR1.CuSavingsS2SourceControl
open Aeneas Aeneas.Std Result AspisR1S2Groups

theorem tau_source (d : Usize) (hd : d.val < 5) :
    ∃ t : Usize, Array.index_usize transport.TAU d = .ok t ∧
      t.val = CuSavingsS2Tables.tau.getD d.val 0 ∧ t.val < 5 := by
  have hlen : d.val < transport.TAU.length := by simpa [transport.TAU] using hd
  obtain ⟨t,ht,hv⟩ := WP.spec_imp_exists (Array.index_usize_spec transport.TAU d hlen)
  refine ⟨t,ht,?_,?_⟩ <;>
    rw [hv] <;>
    interval_cases h : d.val <;>
    simp [transport.TAU,CuSavingsS2Tables.tau,h]

#print axioms tau_source
end AspisR1.CuSavingsS2SourceControl
