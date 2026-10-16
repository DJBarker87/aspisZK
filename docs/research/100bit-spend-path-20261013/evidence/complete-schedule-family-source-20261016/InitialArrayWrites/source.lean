import InitialArrayExecution
import EqualityValueAdapter

/-! The actual schedule's two checked subtracting writes at RATE and RATE+1.
The frame lemma reuses the set/read proof shape already checked for path lanes. -/
set_option autoImplicit false
namespace AspisR1.InitialArrayWrites
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.AbsorptionCallback
open AspisR1.ExtractedMaskQM31Exact
abbrev QM := field.QM31
abbrev Canonical := CurrentCanonicalQM
abbrev RATE := AspisR1InitialCandidate.poseidon2.RATE

theorem read16_success (a : Array QM 16#usize) (i : Usize) (hi : i.val < 16)
    (ha : ∀ j : Fin 16, Canonical (sourceCell a j)) :
    ∃ q, Array.index_usize a i = .ok q ∧ Canonical q ∧
      q = sourceCell a ⟨i.val, hi⟩ := by
  have hb : i.val < a.length := by simpa [a.property] using hi
  obtain ⟨q, hread, hvalue⟩ := WP.spec_imp_exists (Array.index_usize_spec a i hb)
  have hv : q = sourceCell a ⟨i.val, hi⟩ := by simpa [sourceCell] using hvalue
  refine ⟨q, hread, ?_, hv⟩
  rw [hv]
  exact ha ⟨i.val, hi⟩

private theorem sourceCell_set (a : Array QM 16#usize) (i : Usize) (x : QM)
    (j : Fin 16) :
    sourceCell (a.set i x) j = if j.val = i.val then x else sourceCell a j := by
  unfold sourceCell
  by_cases heq : j.val = i.val
  · simp [heq, Array.set_val_eq]
  · have hne : i.val ≠ j.val := Ne.symm heq
    simp [Array.set_val_eq, List.getElem_set_ne, hne, heq]

theorem update16_success (a : Array QM 16#usize) (i : Usize) (x : QM)
    (hi : i.val < 16)
    (ha : ∀ j : Fin 16, Canonical (sourceCell a j)) (hx : Canonical x) :
    ∃ out, Array.update a i x = .ok out ∧
      (∀ j : Fin 16, Canonical (sourceCell out j)) ∧
      ∀ j : Fin 16, sourceCell out j = if j.val = i.val then x else sourceCell a j := by
  have hb : i.val < a.length := by simpa [a.property] using hi
  obtain ⟨out, hupdate, hset⟩ := WP.spec_imp_exists (Array.update_spec a i x hb)
  have hframe : ∀ j : Fin 16,
      sourceCell out j = if j.val = i.val then x else sourceCell a j := by
    intro j
    rw [hset]
    exact sourceCell_set a i x j
  refine ⟨out, hupdate, ?_, hframe⟩
  intro j
  rw [hframe]
  split_ifs
  · exact hx
  · exact ha j

def run (initial : Array QM 16#usize) (low domain length : QM) : Result (Array QM 16#usize) := do
  let current ← Array.index_usize initial RATE
  let subtract ← field.QM31.mul low domain
  let difference ← field.QM31.sub current subtract
  let initial1 ← Array.update initial RATE difference
  let i ← RATE + 1#usize
  let current1 ← Array.index_usize initial1 i
  let subtract1 ← field.QM31.mul low length
  let difference1 ← field.QM31.sub current1 subtract1
  Array.update initial1 i difference1

theorem source_success (initial : Array QM 16#usize) (low domain length : QM)
    (ha : ∀ i : Fin 16, Canonical (sourceCell initial i))
    (hl : Canonical low) (hd : Canonical domain) (hlen : Canonical length) :
    ∃ out, run initial low domain length = .ok out ∧
      (∀ i : Fin 16, Canonical (sourceCell out i)) ∧
      ∀ i : Fin 16, decode (sourceCell out i) =
        if i.val = 8 then decode (sourceCell initial i) - decode low * decode domain
        else if i.val = 9 then decode (sourceCell initial i) - decode low * decode length
        else decode (sourceCell initial i) := by
  have hRATE : RATE.val = 8 := by unfold RATE AspisR1InitialCandidate.poseidon2.RATE; scalar_tac
  have hRateBound : RATE.val < 16 := by rw [hRATE]; omega
  have hFinRate : (⟨RATE.val, hRateBound⟩ : Fin 16) = 8 := by
    apply Fin.ext
    exact hRATE
  obtain ⟨current, hread, hccurrent, hvcurrent⟩ := read16_success initial RATE hRateBound ha
  rw [hFinRate] at hvcurrent
  obtain ⟨subtract, hmul, hcsubtract, hvsubtract⟩ := current_qm_mul_exact low domain hl hd
  obtain ⟨difference, hsub, hcdifference, hvdifference⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact current subtract hccurrent hcsubtract
  obtain ⟨initial1, hupdate, hcinitial1, hframe1⟩ :=
    update16_success initial RATE difference hRateBound ha hcdifference
  simp only [hRATE] at hframe1
  have hAddSpec : (RATE + 1#usize : Result Usize) ⦃ i => i.val = RATE.val + (1#usize).val ⦄ := by
    apply UScalar.add_spec
    rw [hRATE]
    scalar_tac
  obtain ⟨idx, hadd, hidx⟩ := WP.spec_imp_exists hAddSpec
  have hidx9 : idx.val = 9 := by
    have h1 : (1#usize).val = 1 := by scalar_tac
    simpa only [hRATE, h1] using hidx
  have hIdxBound : idx.val < 16 := by rw [hidx9]; omega
  have hFinIdx : (⟨idx.val, hIdxBound⟩ : Fin 16) = 9 := by
    apply Fin.ext
    exact hidx9
  obtain ⟨current1, hread1, hccurrent1, hvcurrent1⟩ :=
    read16_success initial1 idx hIdxBound hcinitial1
  rw [hFinIdx] at hvcurrent1
  have hunchanged9 : sourceCell initial1 (9 : Fin 16) = sourceCell initial (9 : Fin 16) := by
    simpa using hframe1 (9 : Fin 16)
  rw [hunchanged9] at hvcurrent1
  obtain ⟨subtract1, hmul1, hcsubtract1, hvsubtract1⟩ := current_qm_mul_exact low length hl hlen
  obtain ⟨difference1, hsub1, hcdifference1, hvdifference1⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact current1 subtract1 hccurrent1 hcsubtract1
  obtain ⟨out, hupdate1, hcout, hframe2⟩ :=
    update16_success initial1 idx difference1 hIdxBound hcinitial1 hcdifference1
  simp only [hidx9] at hframe2
  change decode difference = decode current - decode subtract at hvdifference
  change decode difference1 = decode current1 - decode subtract1 at hvdifference1
  have hvalue8 : decode difference = decode (sourceCell initial (8 : Fin 16)) - decode low * decode domain := by
    rw [hvdifference, hvcurrent, hvsubtract]
  have hvalue9 : decode difference1 = decode (sourceCell initial (9 : Fin 16)) - decode low * decode length := by
    rw [hvdifference1, hvcurrent1, hvsubtract1]
  refine ⟨out, ?_, hcout, ?_⟩
  · simp only [run, hread, bind_tc_ok, hmul, hsub, hupdate, hadd, hread1, hmul1, hsub1, hupdate1]
  · intro i
    rw [hframe2]
    by_cases hi9 : i.val = 9
    · have hi8 : ¬ i.val = 8 := by omega
      have heq : i = (9 : Fin 16) := Fin.ext hi9
      subst i
      simpa using hvalue9
    · rw [if_neg hi9, hframe1]
      by_cases hi8 : i.val = 8
      · have heq : i = (8 : Fin 16) := Fin.ext hi8
        subst i
        simpa using hvalue8
      · simp only [hi8, hi9, if_false]

#print axioms read16_success
#print axioms update16_success
#print axioms source_success
end
end AspisR1.InitialArrayWrites
