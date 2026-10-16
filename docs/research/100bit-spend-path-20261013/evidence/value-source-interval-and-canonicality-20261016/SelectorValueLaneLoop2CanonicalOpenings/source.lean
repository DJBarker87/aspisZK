import SelectorValueLaneLoops012Slice
import SelectorExpansionCorrectness
import ExtractedMaskQM31SquareExact
import EqualityValueAdapter
import ExtractedMaskQM31Exact

/-! Canonicality preservation for the actual candidate loop 2, assuming its
successful result is observed. This is an intermediate caller contract: it
makes no claim that the loop itself always succeeds. -/
set_option autoImplicit false
namespace AspisR1.SelectorValueLaneLoop2CanonicalOpenings

open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.SelectorExpansionCorrectness

abbrev QM := field.QM31
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Canonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev CanonicalArray {n : Usize} (a : Array QM n) := AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev Loop2 := pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2

private theorem array_index_usize_ok {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

private theorem set_canonical {n : Usize} (a : Array QM n) (i : Usize) (x : QM)
    (ha : CanonicalArray a) (hx : Canonical x) : CanonicalArray (a.set i x) := by
  intro j
  have hjSet : j.val < (a.val.set i.val x).length := by simpa using j.isLt
  have hjOld : j.val < a.val.length := by simpa using j.isLt
  change Canonical ((a.val.set i.val x)[j.val]'hjSet)
  by_cases heq : i.val = j.val
  · have hcell : (a.val.set i.val x)[j.val]'hjSet = x := by
      have hself := List.getElem_set_self (l := a.val) (i := i.val) (a := x)
        (by simpa [heq] using hjSet)
      simpa [heq] using hself
    rw [hcell]
    exact hx
  · have hcell : (a.val.set i.val x)[j.val]'hjSet = a.val[j.val]'hjOld := by
      simpa using (List.getElem_set_ne (l := a.val) (i := i.val) (j := j.val)
        heq hjSet)
    rw [hcell]
    exact ha j

theorem loop2_success_preserves_canonical_fuel_openings
    (fuel : Nat) (openings : Openings) (range : Array QM 33#usize)
    (index : Usize) (outOpen : Openings) (outRange : Array QM 33#usize)
    (hspan : index.val + fuel = 10)
    (hopen : CanonicalArray openings.xor12_z)
    (hrange : CanonicalArray range)
    (hrun : Loop2 openings range index = .ok (outOpen, outRange)) :
    outOpen = openings ∧ CanonicalArray outRange := by
  induction fuel generalizing index range outOpen outRange with
  | zero =>
      have hindex : index.val = 10 := by omega
      have hstop : ¬ index < 10#usize := by scalar_tac
      have hrun' := hrun
      change pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2 openings range index = .ok (outOpen, outRange) at hrun'
      rw [pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2.eq_def] at hrun'
      simp only [if_neg hstop] at hrun'
      have hp := Result.ok.inj hrun'
      have hr : outRange = range := (congrArg Prod.snd hp).symm
      have ho : outOpen = openings := (congrArg Prod.fst hp).symm
      rw [hr]
      exact ⟨ho, hrange⟩
  | succ fuel ih =>
      have hindex : index.val < 10 := by omega
      have hlt : index < 10#usize := by scalar_tac
      have hread : Array.index_usize openings.xor12_z index =
          .ok (openings.xor12_z.val[index.val]'(by
            simpa [openings.xor12_z.property] using (by omega : index.val < 16))) :=
        array_index_usize_ok openings.xor12_z index (by simpa [openings.xor12_z.property] using (by omega : index.val < 16))
      have hq : Canonical (openings.xor12_z.val[index.val]'(by
          simpa [openings.xor12_z.property] using (by omega : index.val < 16))) :=
        hopen ⟨index.val, by simpa [openings.xor12_z.property] using (by omega : index.val < 16)⟩
      obtain ⟨q1, hsq, hq1, _hsqValue⟩ :=
        AspisR1.ExtractedMaskQM31SquareExact.current_qm_square_exact
          (openings.xor12_z.val[index.val]'(by
            simpa [openings.xor12_z.property] using (by omega : index.val < 16))) hq
      obtain ⟨q2, hsub, hq2, _hsubValue⟩ :=
        AspisR1.EqualityValueAdapter.current_qm_sub_exact q1
          (openings.xor12_z.val[index.val]'(by
            simpa [openings.xor12_z.property] using (by omega : index.val < 16))) hq1 hq
      have haddOffsetSpec : (20#usize + index : Result Usize)
          ⦃ dest => dest.val = 20 + index.val ⦄ := by
        apply UScalar.add_spec
        scalar_tac
      obtain ⟨dest, hoffset, hdest⟩ := WP.spec_imp_exists haddOffsetSpec
      have hupdateBound : dest.val < range.length := by
        simpa [range.property, hdest] using (show 20 + index.val < 33 by omega)
      obtain ⟨range1, hupdate, hset⟩ :=
        WP.spec_imp_exists (Array.update_spec range dest q2 hupdateBound)
      have hrange1 : CanonicalArray range1 := by
        rw [hset]
        exact set_canonical range dest q2 hrange hq2
      have haddSpec : (index + 1#usize : Result Usize)
          ⦃ next => next.val = index.val + 1 ⦄ := by
        apply UScalar.add_spec
        scalar_tac
      obtain ⟨index1, hadd, hindex1⟩ := WP.spec_imp_exists haddSpec
      have hrun' := hrun
      change pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2 openings range index = .ok (outOpen, outRange) at hrun'
      rw [pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2.eq_def] at hrun'
      simp only [if_pos hlt, hread, hsq, hsub, hoffset, hupdate, hadd,
        bind_tc_ok] at hrun'
      have hspan1 : index1.val + fuel = 10 := by omega
      exact ih range1 index1 outOpen outRange hspan1
        hrange1 hrun'

#print axioms set_canonical
#print axioms loop2_success_preserves_canonical_fuel_openings
end AspisR1.SelectorValueLaneLoop2CanonicalOpenings
