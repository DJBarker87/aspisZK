import PoseidonExternalLazySourceCut
import PoseidonExternalColumn1CallEquation
import ExtractedMaskCoefficientSchedule
import PoseidonThreeConstantLimbV4
import RawPoseidonExternalRowReads
import Aeneas.Std.WP

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1.PoseidonExternalColumn1Call
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskCoefficientSchedule
open AspisR1.PoseidonThreeConstantLimb
open AspisR1.RawPoseidonExternalRowReads

abbrev U32 := Std.U32
abbrev U64 := Std.U64
abbrev Limbs := Array U32 4#usize
abbrev Sums := Array (Array U64 4#usize) 4#usize
abbrev Closure := state_only_poseidon.external_linear_lazy.closure_1
abbrev wide := AspisR1.PoseidonThreeConstantLimb.wide

def wordAt (a : Array U32 4#usize) (i : Usize) (hi : i.val < 4) : U32 :=
  a.val[i.val]'(by simpa [a.property] using hi)

def sumWordAt (a : Sums) (lane limb : Fin 4) : U64 :=
  let row := a.val[lane.val]'(by simpa [a.property] using lane.isLt)
  row.val[limb.val]'(by simpa [row.property] using limb.isLt)

theorem external_column1_limb_call
    (limbs : Limbs) (sums : Sums) (lane limb : Usize)
    (hlane : lane.val < 16) (hlimb : limb.val < 4)
    (hsums : ∀ i j : Fin 4, (sumWordAt sums i j).val < 2^34) :
    ∃ total : U64,
      state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        (limbs,sums,lane) limb = .ok (total,(limbs,sums,lane)) ∧
      total.val = (wordAt limbs limb hlimb).val +
        (sumWordAt sums ⟨lane.val % 4, Nat.mod_lt _ (by omega)⟩ ⟨limb.val,hlimb⟩).val := by
  have h4 : (4#usize).val = 4 := by scalar_tac
  let word := wordAt limbs limb hlimb
  have hword : Array.index_usize limbs limb = .ok word :=
    array_index_usize_ok limbs limb (by simpa [limbs.property] using hlimb)
  obtain ⟨masked,hmaskedRun,hmaskSpec⟩ :=
    WP.spec_imp_exists (UScalar.and_spec lane (3#usize))
  have hmaskedVal : masked.val = lane.val % 4 :=
    hmaskSpec.1.trans
      (AspisR1.ExtractedMaskCoefficientSchedule.column_and_three_eq_mod_four lane hlane)
  have hmaskedBound : masked.val < 4 := by rw [hmaskedVal]; exact Nat.mod_lt _ (by omega)
  let laneFin : Fin 4 := ⟨lane.val % 4, Nat.mod_lt _ (by omega)⟩
  let limbFin : Fin 4 := ⟨limb.val,hlimb⟩
  have hrowbound : masked.val < (4#usize).val := by simpa [h4] using hmaskedBound
  let row : Array U64 4#usize := sums.val[masked.val]'
    (by simpa [sums.property] using hrowbound)
  have hrow : Array.index_usize sums masked = .ok row :=
    array_index_usize_ok sums masked (by simpa [sums.property] using hrowbound)
  have hrowval : row = sums.val[laneFin.val]'
      (by simpa [sums.property] using laneFin.isLt) := by
    simp [row, laneFin, hmaskedVal]
  have hlimbBound : limb.val < (4#usize).val := by simpa [h4] using hlimb
  let sumWord : U64 := row.val[limb.val]'
    (by simpa [row.property] using hlimbBound)
  have hsumRead : Array.index_usize row limb = .ok sumWord :=
    array_index_usize_ok row limb (by simpa [row.property] using hlimbBound)
  have hsumWord : sumWord = sumWordAt sums laneFin limbFin := by
    simp [sumWordAt, sumWord, hrowval, laneFin, limbFin]
  have hconverted : lift (core.convert.num.FromU64U32.from word) =
      .ok (wide word) := by rfl
  have haddSpec : (wide word + sumWord : Result U64) ⦃z => z.val = (wide word).val + sumWord.val⦄ := by
    apply UScalar.add_spec
    have hw : (wide word).val = word.val := by exact wide_value word
    have hs : sumWord.val < 2^34 := by rw [hsumWord]; exact hsums laneFin limbFin
    have hw32 : word.val < 2^32 := by scalar_tac
    have haddBound : (wide word).val + sumWord.val < 2^64 := by rw [hw]; omega
    scalar_tac
  obtain ⟨total, hadd, htotal⟩ := WP.spec_imp_exists haddSpec
  have hrun : state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      (limbs,sums,lane) limb = .ok (total,(limbs,sums,lane)) := by
    rw [AspisR1.PoseidonExternalColumn1CallEquation.source_eq]
    simp only [hword, hconverted, hmaskedRun, hrow, hsumRead, hadd, bind_tc_ok]
  refine ⟨total, hrun, ?_⟩
  rw [htotal]
  have hw : (wide word).val = word.val := wide_value word
  rw [hw, hsumWord]

#print axioms external_column1_limb_call
end AspisR1.PoseidonExternalColumn1Call
