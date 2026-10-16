import OccupancyGeneratedSlice
import OccupancyExpectedBridge
import R0P.Occupancy
import ExtractedMaskQM31Exact
import ExtractedMaskConstants
import EqualityValueAdapter
import SelectorExpansionCorrectness

/-! Actual checked occupancy lane-11 arithmetic and update, following the
generated eight-lane loop. -/
set_option autoImplicit false
namespace AspisR1.OccupancyLiteralTail
noncomputable section
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskQM31Exact
open AspisR1.ExtractedMaskConstants

abbrev QM := field.QM31
abbrev Canonical := CurrentCanonicalQM
abbrev CanonicalArray {n : Usize} (a : Array QM n) :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact

private theorem bound16 (i : Nat) : i < 16 → i < (16#usize).val := by
  intro hi
  have h16 : (16#usize).val = 16 := by scalar_tac
  omega

private theorem bound12 (i : Nat) : i < 12 → i < (12#usize).val := by
  intro hi
  have h12 : (12#usize).val = 12 := by scalar_tac
  omega

private def get16 (a : Array QM 16#usize) (i : Fin 16) : QM :=
  a.val[i.val]'(by simpa [a.property] using (bound16 i.val i.isLt))

private def get12 (a : Array QM 12#usize) (i : Fin 12) : QM :=
  a.val[i.val]'(by simpa [a.property] using (bound12 i.val i.isLt))

def tailRun (input output : QM) (expected : field.M31)
    (opened : Array QM 16#usize) (occupied oneMinus : QM)
    (occupancy : Array QM 12#usize) : Result (Array QM 12#usize) := do
  let q9 ← Array.index_usize opened 10#usize
  let q10 ← field.QM31.mul q9 oneMinus
  let q11 ← field.QM31.mul input q10
  let q12 ← pool_v1.pair_forest_semantic_terminal.lift_m31 expected
  let q13 ← field.QM31.sub occupied q12
  let q14 ← field.QM31.mul output q13
  let q15 ← field.QM31.add q11 q14
  Array.update occupancy 11#usize q15

private theorem index_ok {α : Type} {n : Usize} (a : Array α n) (i : Usize)
    (hi : i.val < n.val) :
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

private theorem update_ok {n : Usize} (a : Array QM n) (i : Usize) (x : QM)
    (hi : i.val < n.val) :
    ∃ out, Array.update a i x = .ok out ∧ out = a.set i x := by
  exact WP.spec_imp_exists (Array.update_spec a i x (by simpa [a.property] using hi))

theorem tail_success (input output : QM) (expected : field.M31)
    (variant : pool_v1.pair_forest_semantic_terminal.CompiledVariant)
    (opened : Array QM 16#usize) (occupied oneMinus : QM)
    (occupancy : Array QM 12#usize)
    (hin : Canonical input) (hout : Canonical output)
    (hopened : CanonicalArray opened) (hoccupied : Canonical occupied)
    (honeMinus : Canonical oneMinus) (hoccupancy : CanonicalArray occupancy)
    (honeMinusValue : decode oneMinus = 1 - decode occupied)
    (hexpected : pool_v1.pair_forest_semantic_terminal.variant_expected_output variant = .ok expected) :
    ∃ out : Array QM 12#usize,
      tailRun input output expected opened occupied oneMinus occupancy = .ok out ∧
      CanonicalArray out ∧
      decode (get12 out ⟨11, by decide⟩) =
        decode input * (decode (get16 opened ⟨10, by decide⟩) * (1 - decode occupied)) +
        decode output * (decode occupied - R0P.occupancyExpected
          (AspisR1.OccupancyExpectedBridge.modelVariant variant)) ∧
      (∀ j : Fin 12, j.val ≠ 11 → get12 out j = get12 occupancy j) := by
  have h10b : (10#usize).val < (16#usize).val := by scalar_tac
  have hread10 := index_ok opened 10#usize h10b
  let z10 := get16 opened ⟨10, by decide⟩
  have hz10 : Canonical z10 := hopened ⟨10, by simpa [opened.property] using h10b⟩
  have hq10read : Array.index_usize opened 10#usize = .ok z10 := by
    simpa [z10, get16] using hread10
  obtain ⟨expectedM31, q12, hexp, hlift, hq12can, hq12decode⟩ :=
    AspisR1.OccupancyExpectedBridge.variant_expected_lift_exact variant
  have hexpectedM31 : expectedM31 = expected := Result.ok.inj (hexp.symm.trans hexpected)
  subst expectedM31
  obtain ⟨q10, hmul10, hq10can, hq10decode⟩ := current_qm_mul_exact z10 oneMinus hz10 honeMinus
  obtain ⟨q11, hmul11, hq11can, hq11decode⟩ := current_qm_mul_exact input q10 hin hq10can
  obtain ⟨q13, hsub13, hq13can, hq13decode⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact occupied q12 hoccupied hq12can
  obtain ⟨q14, hmul14, hq14can, hq14decode⟩ := current_qm_mul_exact output q13 hout hq13can
  obtain ⟨q15, hadd15, hq15can, hq15decode⟩ := current_qm_add_exact q11 q14 hq11can hq14can
  obtain ⟨out, hupdate, hset⟩ := update_ok occupancy 11#usize q15 (by decide)
  have hcanOut : CanonicalArray out := by
    rw [hset]
    exact set_canonical occupancy 11#usize q15 hoccupancy hq15can
  have hcell : get12 out ⟨11, by decide⟩ = q15 := by
    unfold get12
    rw [hset]
    simp [Array.set_val_eq]
  refine ⟨out, ?_, hcanOut, ?_⟩
  · simp only [tailRun, hq10read, bind_tc_ok, hmul10, hmul11, hlift,
      hsub13, hmul14, hadd15, hupdate]
  · constructor
    · have hq13decode' : decode q13 = decode occupied - decode q12 := by
        change AspisR1.EqualityValueAdapter.decode q13 =
          AspisR1.EqualityValueAdapter.decode occupied - AspisR1.EqualityValueAdapter.decode q12 at hq13decode
        simpa only [AspisR1.EqualityValueAdapter.decode, AspisR1.ExtractedMaskQM31Exact.decode] using hq13decode
      rw [hcell, hq15decode, hq11decode, hq10decode, hq14decode,
        hq13decode', hq12decode, honeMinusValue]
    · intro j hj
      unfold get12
      rw [hset]
      have hne : (11#usize).val ≠ j.val := by
        intro heq
        apply hj
        have h11 : (11#usize).val = 11 := by scalar_tac
        omega
      have hbound : j.val < occupancy.val.length := by
        simpa [occupancy.property] using (bound12 j.val j.isLt)
      have hboundSet : j.val < (occupancy.val.set (11#usize).val q15).length := by
        simpa using hbound
      simpa [Array.set_val_eq] using
        (List.getElem_set_ne (l := occupancy.val) (i := (11#usize).val)
          (j := j.val) hne hboundSet)

#print axioms tail_success
end
end AspisR1.OccupancyLiteralTail
