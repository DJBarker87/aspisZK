import AspisR1.PoseidonClosure2ActualCallFull
import PoseidonClosure2FnMutSource
import ArrayFromFnCopyStable

set_option autoImplicit false
namespace AspisR1.PoseidonClosure2ArrayFromFn
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1PoseidonProjectedClosure2Source

abbrev QM := field.QM31
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev Prepared := field.PreparedQm31Multiplier
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev PreparedFor := AspisR1.ExtractedMaskPreparedState.PreparedFor
abbrev Closure := state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2
abbrev Callback := state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
private def get4 (a : Array QM 4#usize) (i : Usize) (hi : i.val < 4) : QM :=
  a.val[i.val]'(by simpa [a.property] using hi)
private def get3 (a : Array QM 3#usize) (i : Fin 3) : QM :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)
private def getPrepared3 (a : Array Prepared 3#usize) (i : Fin 3) : Prepared :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)
private def i0 : Fin 3 := ⟨0, by omega⟩
private def i1 : Fin 3 := ⟨1, by omega⟩
private def i2 : Fin 3 := ⟨2, by omega⟩

def run (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
    (internalArray : Array QM 16#usize)
    (blockPrepared : Prepared) (weightsPrepared : Array Prepared 3#usize)
    (weights : Array QM 3#usize) (leading full : Array QM 4#usize) :=
  array_from_fn_copy 4#usize field.QM31.Insts.CoreMarkerCopy Callback
    field.QM31.ZERO (openings, internalArray, blockPrepared, weightsPrepared, leading, full)

theorem source_success
    (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
    (internalArray : Array QM 16#usize)
    (blockPrepared : Prepared) (block : QM)
    (weightsPrepared : Array Prepared 3#usize) (weights : Array QM 3#usize)
    (leading full : Array QM 4#usize)
    (hblock : Canonical block)
    (hblockPrepared : PreparedFor blockPrepared block)
    (hweights : ∀ i : Fin 3, Canonical (get3 weights i))
    (hweightsPrepared : ∀ i : Fin 3, PreparedFor (getPrepared3 weightsPrepared i) (get3 weights i))
    (hsuccessor : ∀ i : Fin 16, Canonical
      (openings.succ_z.val[i.val]'(by simpa [openings.succ_z.property] using i.isLt)))
    (hinternal : ∀ i : Fin 16, Canonical
      (internalArray.val[i.val]'(by simpa [internalArray.property] using i.isLt)))
    (hleading : ∀ (i : Usize) (hi : i.val < 4), Canonical (get4 leading i hi))
    (hfull : ∀ (i : Usize) (hi : i.val < 4), Canonical (get4 full i hi)) :
    ∃ out : Array QM 4#usize,
      run openings internalArray blockPrepared weightsPrepared weights leading full = .ok out ∧
      (∀ i : Fin 4, Canonical (out.val[i.val]'(by simpa [out.property] using i.isLt))) ∧
      ∀ i : Fin 4, ∃ target internalPacked leadValue fullValue : QM,
        AspisR1.ExtractedMaskQM31Exact.decode (out.val[i.val]'(by simpa [out.property] using i.isLt)) =
          AspisR1.ExtractedMaskQM31Exact.decode block *
            (AspisR1.ExtractedMaskQM31Exact.decode (get3 weights i0) *
                (AspisR1.ExtractedMaskQM31Exact.decode target - AspisR1.ExtractedMaskQM31Exact.decode leadValue) +
              AspisR1.ExtractedMaskQM31Exact.decode (get3 weights i1) *
                (AspisR1.ExtractedMaskQM31Exact.decode target - AspisR1.ExtractedMaskQM31Exact.decode fullValue) +
              AspisR1.ExtractedMaskQM31Exact.decode (get3 weights i2) *
                (AspisR1.ExtractedMaskQM31Exact.decode target - AspisR1.ExtractedMaskQM31Exact.decode internalPacked)) := by
  classical
  let c : Closure := (openings, internalArray, blockPrepared, weightsPrepared, leading, full)
  have hcallbacks : ∀ i : Fin 4, ∃ out target internalPacked leadValue fullValue : QM,
      Callback.call_mut c
        (UScalar.ofNatCore i.val (by scalar_tac)) =
          .ok (out, c) ∧
      Canonical out ∧
      Decode out = Decode block *
        (Decode (get3 weights i0) * (Decode target - Decode leadValue) +
          Decode (get3 weights i1) * (Decode target - Decode fullValue) +
          Decode (get3 weights i2) * (Decode target - Decode internalPacked)) := by
    intro i
    let idx : Usize := UScalar.ofNatCore i.val (by scalar_tac)
    have hidx : idx.val = i.val := by scalar_tac
    have hbound : idx.val < 4 := by rw [hidx]; exact i.isLt
    obtain ⟨out,target,internalPacked,leadValue,fullValue,ss,hlenS,si,hlenI,
      hcall,hcan,hmodel,hpackS,hmodelS,hpackI,hmodelI,hreadLead,hreadFull⟩ :=
      AspisR1.PoseidonClosure2ActualCallFull.actual_call_success_full
        openings internalArray blockPrepared block weightsPrepared weights leading full idx hbound
        hblock hblockPrepared hweights hweightsPrepared hsuccessor hinternal hleading hfull
    have hidxEq : (UScalar.ofNatCore i.val (by scalar_tac) : Usize) = idx := by
      apply UScalar.eq_of_val_eq
      exact hidx
    have hcall0 : Callback.call_mut c idx = .ok (out, c) := by
      simpa only [Callback, c, state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2,
        AspisR1PoseidonProjectedClosure2Source.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2] using hcall
    have hcall' : Callback.call_mut c (UScalar.ofNatCore i.val (by scalar_tac)) = .ok (out, c) := by
      rw [hidxEq]
      exact hcall0
    exact ⟨out,target,internalPacked,leadValue,fullValue,hcall',hcan,hmodel⟩
  choose values targets internalPackeds leadValues fullValues hcall hcanonical hmodel using hcallbacks
  let value : Nat → QM := fun n => if h : n < 4 then values ⟨n,h⟩ else field.QM31.ZERO
  have hstable : ∀ i : Usize, i.val < (4#usize).val →
      Callback.call_mut c i =
        .ok (value i.val, c) := by
    intro i hi
    have h : i.val < 4 := by simpa using hi
    let fi : Fin 4 := ⟨i.val,h⟩
    have hfi := hcall fi
    have hidxEq : (UScalar.ofNatCore fi.val (by scalar_tac) : Usize) = i := by
      apply UScalar.eq_of_val_eq
      scalar_tac
    rw [hidxEq] at hfi
    simpa only [value, dif_pos h] using hfi
  obtain ⟨out,hrun,hout⟩ := AspisR1SelectedMaskProbe.array_from_fn_copy_stable
    4#usize field.QM31.Insts.CoreMarkerCopy Callback field.QM31.ZERO
    c value hstable
  have hcell : ∀ i : Fin 4, out.val[i.val]'(by simpa [out.property] using i.isLt) = values i := by
    intro i
    have hi : i.val < (4#usize).val := by simpa using i.isLt
    have hh := hout i.val hi
    simpa only [value, dif_pos i.isLt] using hh
  refine ⟨out, ?_, ?_, ?_⟩
  · simpa [run] using hrun
  · intro i
    rw [hcell]
    exact hcanonical i
  · intro i
    refine ⟨targets i, internalPackeds i, leadValues i, fullValues i, ?_⟩
    rw [hcell]
    exact hmodel i

end AspisR1.PoseidonClosure2ArrayFromFn
