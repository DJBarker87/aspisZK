import OccupancyGeneratedSlice
import ExtractedMaskQM31Exact
import ExtractedMaskConstants
import EqualityValueAdapter
import SelectorExpansionCorrectness
import OccupancyExpectedBridge

/-! Actual source prefix for occupancy cells 0, 1 and 2. It executes the
generated reads/arithmetic/updates, deriving every checked success from
canonical inputs. -/
set_option autoImplicit false
namespace AspisR1.OccupancyLiteralPrefixReadsV2
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

def prefixRun (input output : QM) (opened : Array QM 16#usize) :
    Result (QM × QM × QM × QM × Array QM 12#usize) := do
  let occupied ← Array.index_usize opened 0#usize
  let inverse ← Array.index_usize opened 1#usize
  let oneMinus ← field.QM31.sub field.QM31.ONE occupied
  let occupancy := Array.repeat 12#usize field.QM31.ZERO
  let both ← field.QM31.add input output
  let q ← field.QM31.sub occupied field.QM31.ONE
  let q1 ← field.QM31.mul occupied q
  let q2 ← field.QM31.mul both q1
  let occupancy1 ← Array.update occupancy 0#usize q2
  let q3 ← Array.index_usize opened 9#usize
  let q4 ← field.QM31.mul q3 inverse
  let q5 ← field.QM31.sub q4 occupied
  let q6 ← field.QM31.mul both q5
  let occupancy2 ← Array.update occupancy1 1#usize q6
  let q7 ← field.QM31.mul oneMinus inverse
  let q8 ← field.QM31.mul both q7
  let occupancy3 ← Array.update occupancy2 2#usize q8
  .ok (occupied, oneMinus, both, q8, occupancy3)

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

private theorem zero_array_canonical :
    CanonicalArray (Array.repeat 12#usize field.QM31.ZERO) := by
  intro j
  change Canonical ((List.replicate 12 field.QM31.ZERO)[j.val]'(by
    simpa [Array.repeat_val] using j.isLt))
  rw [List.getElem_replicate]
  exact zero_canonical

private theorem update_ok {n : Usize} (a : Array QM n) (i : Usize) (x : QM)
    (hi : i.val < n.val) :
    ∃ out, Array.update a i x = .ok out ∧ out = a.set i x := by
  exact WP.spec_imp_exists (Array.update_spec a i x (by simpa [a.property] using hi))

theorem prefix_success (input output : QM) (opened : Array QM 16#usize)
    (hin : Canonical input) (hout : Canonical output)
    (hopened : CanonicalArray opened) :
    ∃ occupied oneMinus both q8 : QM, ∃ out : Array QM 12#usize,
      prefixRun input output opened = .ok (occupied, oneMinus, both, q8, out) ∧
      Canonical occupied ∧ Canonical oneMinus ∧ Canonical both ∧ Canonical q8 ∧ CanonicalArray out ∧
      decode both = decode input + decode output ∧
      decode (get12 out ⟨0, by decide⟩) =
        (decode input + decode output) * (decode (get16 opened ⟨0, by decide⟩) *
          (decode (get16 opened ⟨0, by decide⟩) - 1)) ∧
      decode (get12 out ⟨1, by decide⟩) =
        (decode input + decode output) *
          (decode (get16 opened ⟨9, by decide⟩) * decode (get16 opened ⟨1, by decide⟩) -
            decode (get16 opened ⟨0, by decide⟩)) ∧
      decode (get12 out ⟨2, by decide⟩) =
        (decode input + decode output) * (decode oneMinus * decode (get16 opened ⟨1, by decide⟩)) ∧
      occupied = get16 opened ⟨0, by decide⟩ ∧
      decode oneMinus = 1 - decode (get16 opened ⟨0, by decide⟩) := by
  have hz0 : Canonical field.QM31.ZERO := zero_canonical
  have ho0 : (0#usize).val = 0 := by scalar_tac
  have ho1 : (1#usize).val = 1 := by scalar_tac
  have ho9 : (9#usize).val = 9 := by scalar_tac
  have hb0 : (0#usize).val < (16#usize).val := by scalar_tac
  have hb1 : (1#usize).val < (16#usize).val := by scalar_tac
  have hb9 : (9#usize).val < (16#usize).val := by scalar_tac
  let occupied := get16 opened ⟨0, by decide⟩
  let inverse := get16 opened ⟨1, by decide⟩
  let nine := get16 opened ⟨9, by decide⟩
  have hread0 : Array.index_usize opened 0#usize = .ok occupied := by
    simpa [occupied, get16] using index_ok opened 0#usize hb0
  have hread1 : Array.index_usize opened 1#usize = .ok inverse := by
    simpa [inverse, get16] using index_ok opened 1#usize hb1
  have hread9 : Array.index_usize opened 9#usize = .ok nine := by
    simpa [nine, get16] using index_ok opened 9#usize hb9
  have hocc : Canonical occupied := hopened ⟨0, by simpa [opened.property] using hb0⟩
  have hinv : Canonical inverse := hopened ⟨1, by simpa [opened.property] using hb1⟩
  have hnine : Canonical nine := hopened ⟨9, by simpa [opened.property] using hb9⟩
  obtain ⟨oneMinus, hone, hcanOneMinus, honeVal⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact field.QM31.ONE occupied one_canonical hocc
  obtain ⟨both, hboth, hcanBoth, hbothVal⟩ := current_qm_add_exact input output hin hout
  obtain ⟨q, hq, hcanQ, hqVal⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact occupied field.QM31.ONE hocc one_canonical
  obtain ⟨q1, hq1, hcanQ1, hq1Val⟩ := current_qm_mul_exact occupied q hocc hcanQ
  obtain ⟨q2, hq2, hcanQ2, hq2Val⟩ := current_qm_mul_exact both q1 hcanBoth hcanQ1
  obtain ⟨a1, ha1, hset1⟩ := update_ok (Array.repeat 12#usize field.QM31.ZERO) 0#usize q2 (by decide)
  have hcanA1 : CanonicalArray a1 := by rw [hset1]; exact set_canonical _ _ _ zero_array_canonical hcanQ2
  obtain ⟨q4, hq4, hcanQ4, hq4Val⟩ := current_qm_mul_exact nine inverse hnine hinv
  obtain ⟨q5, hq5, hcanQ5, hq5Val⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact q4 occupied hcanQ4 hocc
  obtain ⟨q6, hq6, hcanQ6, hq6Val⟩ := current_qm_mul_exact both q5 hcanBoth hcanQ5
  obtain ⟨a2, ha2, hset2⟩ := update_ok a1 1#usize q6 (by decide)
  have hcanA2 : CanonicalArray a2 := by rw [hset2]; exact set_canonical _ _ _ hcanA1 hcanQ6
  obtain ⟨q7, hq7, hcanQ7, hq7Val⟩ := current_qm_mul_exact oneMinus inverse hcanOneMinus hinv
  obtain ⟨q8, hq8, hcanQ8, hq8Val⟩ := current_qm_mul_exact both q7 hcanBoth hcanQ7
  obtain ⟨out, hout, hset3⟩ := update_ok a2 2#usize q8 (by decide)
  have hone' : field.QM31.sub field.QM31.ONE occupied = .ok oneMinus := hone
  have hboth' : field.QM31.add input output = .ok both := hboth
  have hq' : field.QM31.sub occupied field.QM31.ONE = .ok q := hq
  have hq1' : field.QM31.mul occupied q = .ok q1 := hq1
  have hq4' : field.QM31.mul nine inverse = .ok q4 := hq4
  have hq7' : field.QM31.mul oneMinus inverse = .ok q7 := hq7
  have hoccGet : occupied = get16 opened ⟨0, by decide⟩ := rfl
  have hinvGet : inverse = get16 opened ⟨1, by decide⟩ := rfl
  have hnineGet : nine = get16 opened ⟨9, by decide⟩ := rfl
  have hqVal' : decode q = decode occupied - decode field.QM31.ONE := by
    change AspisR1.EqualityValueAdapter.decode q =
      AspisR1.EqualityValueAdapter.decode occupied -
        AspisR1.EqualityValueAdapter.decode field.QM31.ONE at hqVal
    simpa only [AspisR1.EqualityValueAdapter.decode, AspisR1.ExtractedMaskQM31Exact.decode] using hqVal
  have hq5Val' : decode q5 = decode q4 - decode occupied := by
    change AspisR1.EqualityValueAdapter.decode q5 =
      AspisR1.EqualityValueAdapter.decode q4 - AspisR1.EqualityValueAdapter.decode occupied at hq5Val
    simpa only [AspisR1.EqualityValueAdapter.decode, AspisR1.ExtractedMaskQM31Exact.decode] using hq5Val
  have honeVal' : decode oneMinus = decode field.QM31.ONE - decode occupied := by
    change AspisR1.EqualityValueAdapter.decode oneMinus =
      AspisR1.EqualityValueAdapter.decode field.QM31.ONE -
        AspisR1.EqualityValueAdapter.decode occupied at honeVal
    simpa only [AspisR1.EqualityValueAdapter.decode, AspisR1.ExtractedMaskQM31Exact.decode] using honeVal
  have hcanOut : CanonicalArray out := by
    rw [hset3]
    exact set_canonical a2 2#usize q8 hcanA2 hcanQ8
  have hcell0 : get12 out ⟨0, by decide⟩ = q2 := by
    unfold get12
    rw [hset3, hset2, hset1]
    simp [Array.set_val_eq]
  have hcell1 : get12 out ⟨1, by decide⟩ = q6 := by
    unfold get12
    rw [hset3, hset2]
    simp [Array.set_val_eq, hset1]
  have hcell2 : get12 out ⟨2, by decide⟩ = q8 := by
    unfold get12
    rw [hset3]
    simp [Array.set_val_eq]
  refine ⟨occupied, oneMinus, both, q8, out, ?_, hocc, hcanOneMinus, hcanBoth, hcanQ8,
    hcanOut, hbothVal, ?_, ?_, ?_, ?_, ?_⟩
  · have ha1' : Array.update (Array.repeat 12#usize field.QM31.ZERO)
        0#usize q2 = .ok a1 := ha1
    have ha2' : Array.update a1 1#usize q6 = .ok a2 := ha2
    have hout' : Array.update a2 2#usize q8 = .ok out := hout
    change (do
      let occupied ← Array.index_usize opened 0#usize
      let inverse ← Array.index_usize opened 1#usize
      let oneMinus ← field.QM31.sub field.QM31.ONE occupied
      let occupancy := Array.repeat 12#usize field.QM31.ZERO
      let both ← field.QM31.add input output
      let q ← field.QM31.sub occupied field.QM31.ONE
      let q1 ← field.QM31.mul occupied q
      let q2 ← field.QM31.mul both q1
      let occupancy1 ← Array.update occupancy 0#usize q2
      let q3 ← Array.index_usize opened 9#usize
      let q4 ← field.QM31.mul q3 inverse
      let q5 ← field.QM31.sub q4 occupied
      let q6 ← field.QM31.mul both q5
      let occupancy2 ← Array.update occupancy1 1#usize q6
      let q7 ← field.QM31.mul oneMinus inverse
      let q8 ← field.QM31.mul both q7
      let occupancy3 ← Array.update occupancy2 2#usize q8
      .ok (occupied, oneMinus, both, q8, occupancy3)) = .ok (occupied, oneMinus, both, q8, out)
    simp only [hread0, hread1, bind_tc_ok, hone', hboth', hq', hq1', hq2,
      ha1', hread9, hq4', hq5, hq6, ha2', hq7', hq8, hout']
  · rw [hcell0, hq2Val, hq1Val, hqVal', hbothVal, hoccGet, one_decode]
  · rw [hcell1, hq6Val, hq5Val', hq4Val, hbothVal, hnineGet, hinvGet, hoccGet]
  · rw [hcell2, hq8Val, hq7Val, hbothVal, hinvGet]
  · rfl
  · rw [honeVal', one_decode, hoccGet]

#print axioms prefix_success

end
end AspisR1.OccupancyLiteralPrefixReadsV2
