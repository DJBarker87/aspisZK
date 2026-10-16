import SelectorValueLaneFullRangeValues
import SelectorValueLaneValueRangeListFacts
import R0P.Value

/-! The source-produced 33-cell array is identified with the exact
`R0P.valueRange` list. This is the range-side endpoint consumed by the
residual-list and packing bridges. -/
set_option autoImplicit false
namespace AspisR1.SelectorValueLaneRangeListCorrespondence

open Aeneas Aeneas.Std
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev CanonicalArray {n : Usize} (a : Array QM n) :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev cell := AspisR1.SelectorValueLanePreprocessMeaning.cell
abbrev exactOpenings := AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings

theorem generated_range_list_eq_valueRange
    (openings : Openings)
    (hopenZ : CanonicalArray openings.z)
    (hopenSucc : CanonicalArray openings.succ_z)
    (hopenXor : CanonicalArray openings.xor12_z) :
    ∃ range6 : Array QM 33#usize,
      CanonicalArray range6 ∧
      AspisR1.SelectorValueLaneFullRangeValues.rangePrefixConstruction openings =
        .ok range6 ∧
      List.ofFn (fun i : Fin 33 => cell range6 i) =
        R0P.valueRange (exactOpenings openings) := by
  obtain ⟨r1, r2, r3, reconstructed, q11, q12, q13, q14,
    r4, r5, range6, h0, h1, h2, hq12, hu30, hu31, hu32,
    hconstruction, hfirst, hsecond, hthird, h30, h31, h32,
    hq12value, hcanonical⟩ :=
    AspisR1.SelectorValueLaneFullRangeValues.generated_full_range_values
      openings hopenZ hopenSucc hopenXor
  refine ⟨range6, hcanonical, hconstruction, ?_⟩
  apply List.ext_getElem
  · simp [R0P.valueRange]
  · intro n hleft hright
    have hn : n < 33 := by simpa [R0P.valueRange] using hright
    rw [List.getElem_ofFn]
    by_cases h0n : n < 10
    · let i : Fin 10 := ⟨n, h0n⟩
      have harray : cell range6 ⟨n, by omega⟩ =
          (exactOpenings openings).z (i.castAdd 6)^2 -
            (exactOpenings openings).z (i.castAdd 6) := by
        simpa [i] using hfirst i
      have hlist := AspisR1.SelectorValueLaneValueRangeListFacts.first_block
        (exactOpenings openings) i
      have hlistn : (R0P.valueRange (exactOpenings openings))[n]'hright =
          (exactOpenings openings).z (i.castAdd 6)^2 -
            (exactOpenings openings).z (i.castAdd 6) := by
        simpa [i] using hlist
      exact harray.trans hlistn.symm
    · by_cases h1n : n < 20
      · have hn10 : 10 ≤ n := by omega
        let i : Fin 10 := ⟨n - 10, by omega⟩
        have hi : 10 + i.val = n := by simp [i, hn10]
        have harray : cell range6 ⟨n, by omega⟩ =
            (exactOpenings openings).succ (i.castAdd 6)^2 -
              (exactOpenings openings).succ (i.castAdd 6) := by
          have hidx : (⟨n, by omega⟩ : Fin 33) = ⟨10 + i.val, by omega⟩ :=
            Fin.ext hi.symm
          rw [hidx]
          exact hsecond i
        have hlist := AspisR1.SelectorValueLaneValueRangeListFacts.second_block
          (exactOpenings openings) i
        have hlistn : (R0P.valueRange (exactOpenings openings))[n]'hright =
            (exactOpenings openings).succ (i.castAdd 6)^2 -
              (exactOpenings openings).succ (i.castAdd 6) := by
          simpa only [hi] using hlist
        exact harray.trans hlistn.symm
      · by_cases h2n : n < 30
        · have hn20 : 20 ≤ n := by omega
          let i : Fin 10 := ⟨n - 20, by omega⟩
          have hi : 20 + i.val = n := by simp [i, hn20]
          have harray : cell range6 ⟨n, by omega⟩ =
              (exactOpenings openings).xor12 (i.castAdd 6)^2 -
                (exactOpenings openings).xor12 (i.castAdd 6) := by
            have hidx : (⟨n, by omega⟩ : Fin 33) = ⟨20 + i.val, by omega⟩ :=
              Fin.ext hi.symm
            rw [hidx]
            exact hthird i
          have hlist := AspisR1.SelectorValueLaneValueRangeListFacts.third_block
            (exactOpenings openings) i
          have hlistn : (R0P.valueRange (exactOpenings openings))[n]'hright =
              (exactOpenings openings).xor12 (i.castAdd 6)^2 -
                (exactOpenings openings).xor12 (i.castAdd 6) := by
            simpa only [hi] using hlist
          exact harray.trans hlistn.symm
        · have hn30 : 30 ≤ n := by omega
          have hle : n ≤ 32 := by omega
          interval_cases n
          · have htail :=
              AspisR1.SelectorValueLaneValueRangeListFacts.reconstruction_tail
                (exactOpenings openings)
            have h30' : cell range6 ⟨30, by decide⟩ =
                AspisR1.ExtractedMaskQM31Exact.decode q12 := by
              change cell range6 ⟨30, by decide⟩ =
                AspisR1.ExtractedMaskQM31Exact.decode q12 at h30
              exact h30
            have hz10 : AspisR1.SelectorValueLaneFullRangeValues.exactZ10 openings =
                (exactOpenings openings).z ⟨10, by decide⟩ := rfl
            have hzmodel : AspisR1.SelectorValueLaneTailExecution.reconstructModel openings.z =
                R0P.valueReconstruct10 (exactOpenings openings).z := by rfl
            have hsuccmodel : AspisR1.SelectorValueLaneTailExecution.reconstructModel openings.succ_z =
                R0P.valueReconstruct10 (exactOpenings openings).succ := by rfl
            have hxormodel : AspisR1.SelectorValueLaneTailExecution.reconstructModel openings.xor12_z =
                R0P.valueReconstruct10 (exactOpenings openings).xor12 := by rfl
            have hscale10 : AspisR1.SelectorValueLaneTailExecution.scale10 =
                AspisR1.SelectorValueLaneTailConstants.scale10 := rfl
            have hscale20 : AspisR1.SelectorValueLaneTailExecution.scale20 =
                AspisR1.SelectorValueLaneTailConstants.scale20 := rfl
            have hscales := AspisR1.SelectorValueLaneTailConstants.source_shift_embeddings
            have harray : cell range6 ⟨30, by decide⟩ =
                (exactOpenings openings).z ⟨10, by decide⟩ -
                  (R0P.valueReconstruct10 (exactOpenings openings).z +
                    R0P.valueReconstruct10 (exactOpenings openings).succ * 1024 +
                    R0P.valueReconstruct10 (exactOpenings openings).xor12 * 1048576) := by
              rw [h30', hq12value, hz10, hzmodel, hsuccmodel, hxormodel,
                hscale10, hscale20, hscales.1, hscales.2]
            exact harray.trans htail.symm
          · have htail :=
              AspisR1.SelectorValueLaneValueRangeListFacts.succ_tail
                (exactOpenings openings)
            exact h31.trans htail.symm
          · have htail :=
              AspisR1.SelectorValueLaneValueRangeListFacts.xor_tail
                (exactOpenings openings)
            exact h32.trans htail.symm

#print axioms generated_range_list_eq_valueRange
end AspisR1.SelectorValueLaneRangeListCorrespondence
