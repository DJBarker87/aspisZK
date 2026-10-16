import PreweightedClosureSlice
import ExtractedMaskReducerOps

/-! Success and exact zero-padded source-lane selection for the actual
add_preweighted closure. This covers its checked index arithmetic and reads;
it is consumed by the retained stable from_fn-copy theorem. -/
set_option autoImplicit false
namespace AspisR1.PreweightedClosureSuccess
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskReducerOps

abbrev QM := field.QM31

/-- Total view used only to state the mathematical lane-selection result. -/
def sourceCell {N : Usize} (values : Array QM N) (n : Nat) : QM :=
  if h : n < N.val then values.val[n]'(by simpa [values.property] using h)
  else field.QM31.ZERO

def selectedCell {N : Usize} (values : Array QM N)
    (start group slot : Nat) : QM :=
  if start ≤ 4 * group + slot ∧ 4 * group + slot < start + N.val then
    sourceCell values (4 * group + slot - start)
  else field.QM31.ZERO

private theorem index_ok {T : Type} {N : Usize}
    (values : Array T N) (i : Usize) (hi : i.val < N.val) :
    Array.index_usize values i =
      .ok (values.val[i.val]'(by simpa [values.property] using hi)) := by
  have hidx : i.val < values.val.length := by simpa [values.property] using hi
  unfold Array.index_usize
  change (match values.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (values.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

theorem call_mut_success {N : Usize}
    (values : Array QM N) (group start slot : Usize)
    (hgroup : group.val < 24) (hslot : slot.val < 4)
    (hinterval : start.val + N.val ≤ 96) :
    AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      (group, start, values) slot =
      .ok (selectedCell values start.val group.val slot.val,
        (group, start, values)) := by
  have hmax : 96 ≤ Usize.max := by
    have h := Usize.cMax_bound_concrete.1
    omega
  have hmulSpec : (4#usize * group : Result Usize) ⦃ z => z.val = 4 * group.val ⦄ := by
    apply Usize.mul_spec
    have hfour : (4#usize).val = 4 := by scalar_tac
    rw [hfour]
    omega
  obtain ⟨base, hmul, hbase⟩ := WP.spec_imp_exists hmulSpec
  have haddSpec : (base + slot : Result Usize) ⦃ z => z.val = base.val + slot.val ⦄ := by
    apply Usize.add_spec
    omega
  obtain ⟨source, hadd, hsource⟩ := WP.spec_imp_exists haddSpec
  have hsourceNat : source.val = 4 * group.val + slot.val := by omega
  have hendSpec : (start + N : Result Usize) ⦃ z => z.val = start.val + N.val ⦄ := by
    apply Usize.add_spec
    omega
  obtain ⟨last, hend, hlast⟩ := WP.spec_imp_exists hendSpec
  unfold AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  simp only [hmul, bind_tc_ok, hadd, bind_tc_ok]
  by_cases hlo : start.val ≤ source.val
  · have hge : source ≥ start := by exact hlo
    simp only [if_pos hge, hend, bind_tc_ok]
    by_cases hhi : source.val < last.val
    · have hlt : source < last := by exact hhi
      obtain ⟨idx, hsub, hidx⟩ := sub_success source start hlo
      have hidxN : idx.val < N.val := by omega
      have hread := index_ok values idx hidxN
      simp only [if_pos hlt]
      change (do
        let idx' ← UScalar.sub source start
        let q ← Array.index_usize values idx'
        Result.ok (q, (group, start, values))) =
          Result.ok (selectedCell values start.val group.val slot.val,
            (group, start, values))
      simp only [hsub, bind_tc_ok, hread, bind_tc_ok]
      have hselected : selectedCell values start.val group.val slot.val =
          values.val[idx.val]'(by simpa [values.property] using hidxN) := by
        unfold selectedCell sourceCell
        rw [if_pos (by omega), dif_pos (by omega)]
        congr 1
        omega
      rw [hselected]
    · have hnlt : ¬ source < last := by exact hhi
      simp only [if_neg hnlt]
      have hselected : selectedCell values start.val group.val slot.val = field.QM31.ZERO := by
        unfold selectedCell
        rw [if_neg (by omega)]
      rw [hselected]
  · have hnge : ¬ source ≥ start := by exact hlo
    simp only [if_neg hnge]
    have hselected : selectedCell values start.val group.val slot.val = field.QM31.ZERO := by
      unfold selectedCell
      rw [if_neg (by omega)]
    rw [hselected]

#print axioms call_mut_success
end AspisR1.PreweightedClosureSuccess
