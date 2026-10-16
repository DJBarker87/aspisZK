import ValueConservationArithmetic
import PreweightedWrapperModel

/-! Factored exact conservation-tail expression from the generated
add_value_lanes body, after its conservation selector is obtained. The reads,
arithmetic and final packed-array call are all discharged by source contracts;
selector construction and the enclosing caller remain separate. -/
set_option autoImplicit false
namespace AspisR1.ValueConservationTail
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate
open AspisR1.PreweightedLoopModel
open AspisR1.ExtractedMaskQM31Exact

abbrev Canonical := CurrentCanonicalQM

def cellAt (a : Array QM 16#usize) (j : Fin 16) : QM :=
  a.val[j.val]'(by simpa [a.property] using j.isLt)

def run (packed : Array QM 24#usize) (selector : QM)
    (z succ : Array QM 16#usize) : Result (Array QM 24#usize) := do
  let q15 ← Array.index_usize z 0#usize
  let q16 ← Array.index_usize z 1#usize
  let q17 ← field.QM31.sub q15 q16
  let q18 ← Array.index_usize z 2#usize
  let q19 ← field.QM31.sub q17 q18
  let q20 ← field.QM31.mul selector q19
  let q21 ← Array.index_usize succ 0#usize
  let q22 ← Array.index_usize succ 1#usize
  let q23 ← field.QM31.sub q21 q22
  let q24 ← field.QM31.mul selector q23
  AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted
    packed 82#usize (Array.make 2#usize [q20, q24])

private theorem index_ok (a : Array QM 16#usize) (i : Usize) (j : Fin 16)
    (hij : i.val = j.val) : Array.index_usize a i = .ok (cellAt a j) := by
  have hb : i.val < a.length := by rw [hij]; simpa using j.isLt
  obtain ⟨q, hread, hvalue⟩ := WP.spec_imp_exists (Array.index_usize_spec a i hb)
  rw [hread]
  congr 1
  rw [hvalue]
  simp only [cellAt, hij]

theorem run_success (packed : Array QM 24#usize) (selector : QM)
    (z succ : Array QM 16#usize)
    (hpacked : CanonicalArray packed) (hselector : Canonical selector)
    (hz : CanonicalArray z) (hsucc : CanonicalArray succ) :
    ∃ r0 r1 : QM, ∃ out : Array QM 24#usize,
      run packed selector z succ = .ok out ∧ CanonicalArray out ∧
      CanonicalArray (Array.make 2#usize [r0, r1]) ∧
      decoded out = (fun j => decoded packed j +
        groupValue (Array.make 2#usize [r0, r1]) 82 j.val) ∧
      decode r0 = decode selector *
        ((decode (cellAt z 0) - decode (cellAt z 1)) - decode (cellAt z 2)) ∧
      decode r1 = decode selector * (decode (cellAt succ 0) - decode (cellAt succ 1)) := by
  have hcz (j : Fin 16) : Canonical (cellAt z j) := hz j
  have hcs (j : Fin 16) : Canonical (cellAt succ j) := hsucc j
  obtain ⟨d01, d012, r0, ds, r1, hd01, hd012, hr0, hds, hr1, harray, hv0, hv1⟩ :=
    AspisR1.ValueConservationArithmetic.conservation_success selector
      (cellAt z 0) (cellAt z 1) (cellAt z 2) (cellAt succ 0) (cellAt succ 1)
      hselector (hcz 0) (hcz 1) (hcz 2) (hcs 0) (hcs 1)
  obtain ⟨out, hpack, hcanon, hmodel⟩ :=
    AspisR1.PreweightedWrapperModel.add_preweighted_model packed 82#usize
      (Array.make 2#usize [r0, r1]) (by decide) (by decide) hpacked harray
  refine ⟨r0, r1, out, ?_, hcanon, harray, hmodel, hv0, hv1⟩
  have hz0 := index_ok z 0#usize 0 rfl
  have hz1 := index_ok z 1#usize 1 rfl
  have hz2 := index_ok z 2#usize 2 rfl
  have hs0 := index_ok succ 0#usize 0 rfl
  have hs1 := index_ok succ 1#usize 1 rfl
  unfold run
  simp only [hz0, hz1, hz2, hs0, hs1, hd01, hd012, hr0, hds, hr1,
    bind_tc_ok, hpack]

#print axioms run_success
end AspisR1.ValueConservationTail
