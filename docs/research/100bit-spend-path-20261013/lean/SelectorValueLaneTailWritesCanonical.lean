import SelectorValueLaneLoops012Slice
import SelectorExpansionCorrectness

/-! Canonicality of the three literal tail writes (indices 30–32) used by the
candidate `add_value_lanes` parent. The reconstructed value at index 30 is a
separate field-arithmetic obligation; the two copied opening cells are derived
canonical from their successful source reads. -/
set_option autoImplicit false
namespace AspisR1.SelectorValueLaneTailWritesCanonical

open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.SelectorExpansionCorrectness

abbrev QM := field.QM31
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Canonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev CanonicalArray {n : Usize} (a : Array QM n) : Prop :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray a

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

private theorem update_success_canonical {n : Usize} (a : Array QM n)
    (i : Usize) (x : QM) (result : Array QM n)
    (ha : CanonicalArray a) (hx : Canonical x)
    (hbound : i.val < a.length)
    (hrun : Array.update a i x = .ok result) : CanonicalArray result := by
  obtain ⟨updated, hspec, hset⟩ := WP.spec_imp_exists (Array.update_spec a i x hbound)
  have heq : updated = result := Result.ok.inj (hspec.symm.trans hrun)
  rw [← heq, hset]
  exact set_canonical a i x ha hx

theorem tail_three_updates_canonical
    (openings : Openings) (range3 range4 range5 range6 : Array QM 33#usize)
    (q8 q13 q14 : QM)
    (hopenSucc : CanonicalArray openings.succ_z)
    (hopenXor : CanonicalArray openings.xor12_z)
    (hrange3 : CanonicalArray range3)
    (hq8 : Canonical q8)
    (hupdate30 : Array.update range3 30#usize q8 = .ok range4)
    (hread13 : Array.index_usize openings.succ_z 10#usize = .ok q13)
    (hupdate31 : Array.update range4 31#usize q13 = .ok range5)
    (hread14 : Array.index_usize openings.xor12_z 10#usize = .ok q14)
    (hupdate32 : Array.update range5 32#usize q14 = .ok range6) :
    CanonicalArray range6 := by
  have hread13' := array_index_usize_ok openings.succ_z 10#usize (by scalar_tac)
  have hq13eq : q13 = openings.succ_z.val[10]'(by
      simpa [openings.succ_z.property] using (by scalar_tac : (10#usize).val < 16)) :=
    Result.ok.inj (hread13.symm.trans hread13')
  have hq13 : Canonical q13 := by
    rw [hq13eq]
    exact hopenSucc ⟨10, by simpa [openings.succ_z.property] using
      (by scalar_tac : (10#usize).val < 16)⟩
  have hread14' := array_index_usize_ok openings.xor12_z 10#usize (by scalar_tac)
  have hq14eq : q14 = openings.xor12_z.val[10]'(by
      simpa [openings.xor12_z.property] using (by scalar_tac : (10#usize).val < 16)) :=
    Result.ok.inj (hread14.symm.trans hread14')
  have hq14 : Canonical q14 := by
    rw [hq14eq]
    exact hopenXor ⟨10, by simpa [openings.xor12_z.property] using
      (by scalar_tac : (10#usize).val < 16)⟩
  have hrange4 : CanonicalArray range4 :=
    update_success_canonical range3 30#usize q8 range4 hrange3 hq8 (by scalar_tac) hupdate30
  have hrange5 : CanonicalArray range5 :=
    update_success_canonical range4 31#usize q13 range5 hrange4 hq13 (by scalar_tac) hupdate31
  exact update_success_canonical range5 32#usize q14 range6 hrange5 hq14
    (by scalar_tac) hupdate32

#print axioms tail_three_updates_canonical
end AspisR1.SelectorValueLaneTailWritesCanonical
