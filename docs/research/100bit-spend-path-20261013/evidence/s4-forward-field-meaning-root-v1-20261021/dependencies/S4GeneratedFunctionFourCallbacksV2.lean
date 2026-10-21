import S4AllFourSourceFieldFourOutputsV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1FastDotsGeneratedFunctionFourCallbacksV2

abbrev Ops := AspisR1FastDotsAllFourSourceFieldFourOutputsV1.Ops
abbrev Wide := AspisR1FastDotsAllFourSourceFieldFourOutputsV1.Wide
abbrev CallbackDecodedTrace :=
  AspisR1FastDotsAllFourSourceFieldFourOutputsV1.CallbackDecodedTrace

def bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β} {x : β}
    (h : Bind.bind r f = .ok x) : ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

/-- The generated `fast_dots::four_dots` call's success exposes the parsed
608-byte fixed array used by its N=4 callback array. The successful source operations identify this array with the exact 608-byte
Slice prefix consumed by the original generated function. -/
theorem generated_four_dots_success_four_callback_traces
    (base : Ops) (q : Slice Std.U8) (g : Array Wide 29#usize)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsHeadTailSharedWitnessRootV2.CoordBound
        (g.val[i.val]'(by simpa [g.property] using i.isLt)))
    {values : Array Wide 4#usize}
    (h : AspisR1FastDotsCurrent.fast_dots.four_dots
      (AspisR1FastDotsAllFourHeadDecodingV1.Outer base) q g = .ok values) :
    ∃ arrayQ : Array Std.U8 608#usize,
      arrayQ.val = q.val.slice 0 (608#usize) ∧
      (AspisR1FastDotsAllFourHeadDecodingV1.Outer base).arrayFromFn 4#usize
        (AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
          (AspisR1FastDotsAllFourHeadDecodingV1.Outer base)) (arrayQ,g) = .ok values ∧
      ∃ v0 v1 v2 v3 : Wide,
        values.val = [v0,v1,v2,v3] ∧
        CallbackDecodedTrace base
          (AspisR1FastDotsConcreteTailInstallRootV1.install
            (AspisR1FastDotsAllFourHeadDecodingV1.Outer base)) arrayQ g 0#usize v0 ∧
        CallbackDecodedTrace base
          (AspisR1FastDotsConcreteTailInstallRootV1.install
            (AspisR1FastDotsAllFourHeadDecodingV1.Outer base)) arrayQ g 1#usize v1 ∧
        CallbackDecodedTrace base
          (AspisR1FastDotsConcreteTailInstallRootV1.install
            (AspisR1FastDotsAllFourHeadDecodingV1.Outer base)) arrayQ g 2#usize v2 ∧
        CallbackDecodedTrace base
          (AspisR1FastDotsConcreteTailInstallRootV1.install
            (AspisR1FastDotsAllFourHeadDecodingV1.Outer base)) arrayQ g 3#usize v3 := by
  unfold AspisR1FastDotsCurrent.fast_dots.four_dots at h
  rcases bind_ok_inv h with ⟨slice608, hslice, hrest⟩
  rcases bind_ok_inv hrest with ⟨parsed, hparsed, hrest⟩
  rcases bind_ok_inv hrest with ⟨arrayQ, hunwrap, harray⟩
  have hsliceBytes : slice608.val = q.val.slice 0 (608#usize) := by
    have hs := hslice
    change core.slice.index.SliceIndexRangeToUsizeSlice.index
      { «end» := 608#usize } q = .ok slice608 at hs
    by_cases hh : (608#usize) ≤ q.length
    · simp only [core.slice.index.SliceIndexRangeToUsizeSlice.index, if_pos hh] at hs
      exact (congrArg (fun s : Slice Std.U8 => s.val) (Result.ok.inj hs)).symm
    · simp only [core.slice.index.SliceIndexRangeToUsizeSlice.index, if_neg hh] at hs
      cases hs
  have hparsedOk : parsed = .Ok arrayQ := by
    cases parsed with
    | Ok actual =>
      have hOk : Result.ok actual = Result.ok arrayQ := by
        simpa only [core.result.Result.unwrap] using hunwrap
      exact congrArg core.result.Result.Ok (Result.ok.inj hOk)
    | Err e =>
      simp only [core.result.Result.unwrap] at hunwrap
      cases hunwrap
  have harrayVal : arrayQ.val = slice608.val := by
    have ht := hparsed
    rw [hparsedOk] at ht
    by_cases hlen : slice608.len = 608#usize
    · simp [core.array.TryFromSharedArraySlice.try_from, hlen] at ht
      exact (congrArg (fun a : Array Std.U8 608#usize => a.val) ht).symm
    · simp [core.array.TryFromSharedArraySlice.try_from, hlen] at ht
  have hfour :=
    AspisR1FastDotsAllFourSourceFieldFourOutputsV1.generated_outer_success_four_callback_decoded_traces
      base arrayQ g hcoords harray
  exact ⟨arrayQ, harrayVal.trans hsliceBytes, harray, hfour⟩

#print axioms generated_four_dots_success_four_callback_traces

end AspisR1FastDotsGeneratedFunctionFourCallbacksV2
