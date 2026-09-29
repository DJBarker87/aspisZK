import V7CallerCurrentReleaseR26TerminalDotSource
import V7CallerCurrentReleaseR26AcceptedRelationRoundsSemantics

/-!
# Terminal four-value source prefix

The generated accepted terminal edge obtains its values by slicing entries
zero through three from the fixed 256-cell backing array.  This file records
the slice's exact length, canonicality, and maintained K1 interpretation.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TerminalPrefixSemantics

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26K1QueryWeightBridge
open V7CallerCurrentReleaseR26FoldValuesPrefixSemantics
open V7CallerCurrentReleaseR26K1FoldValuesPrefixBridge
open V7CallerCurrentReleaseR26TerminalStructuredComponents

abbrev RawQM31 := field.QM31

local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

theorem terminal_prefix_corresponds
    (values : Array RawQM31 256#usize) (terminalSlice : Slice RawQM31)
    (canonical : CanonicalValues values)
    (run : core.array.Array.index
        (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice RawQM31))
        values { «end» := 4#usize } = ok terminalSlice) :
    terminalSlice.length = 4 ∧
      CanonicalSlice terminalSlice ∧
      terminalValues terminalSlice = modelPrefix values 4 := by
  have bound : (4#usize : Std.Usize) ≤ (Array.to_slice values).length := by
    rw [Slice.length]
    norm_num [Array.to_slice, Array.length_eq]
  have prefixExact : terminalSlice =
      ⟨values.val.slice 0 (4#usize).val, by scalar_tac⟩ := by
    apply Result.ok.inj
    calc
      ok terminalSlice = core.array.Array.index
          (core.ops.index.IndexSlice
            (core.slice.index.SliceIndexRangeToUsizeSlice RawQM31))
          values { «end» := 4#usize } := run.symm
      _ = core.slice.index.SliceIndexRangeToUsizeSlice.index
          { «end» := 4#usize } (Array.to_slice values) := by rfl
      _ = ok ⟨values.val.slice 0 (4#usize).val, by scalar_tac⟩ := by
        unfold core.slice.index.SliceIndexRangeToUsizeSlice.index
        rw [if_pos bound]
        rfl
  have prefixValExact : terminalSlice.val = values.val.take 4 := by
    calc
      terminalSlice.val = values.val.slice 0 (4#usize).val :=
        congrArg (fun slice : Slice RawQM31 => slice.val) prefixExact
      _ = values.val.take 4 := by norm_num [List.slice]
  have sliceLength : terminalSlice.length = 4 := by
    rw [Slice.length, prefixValExact]
    simp
  refine ⟨sliceLength, ?_, ?_⟩
  · intro index indexBound
    have indexFour : index < 4 := by
      rw [sliceLength] at indexBound
      exact indexBound
    have sourceBound : index < 256 := by
      omega
    have listBound : index < values.val.length := by
      simpa [Array.length_eq] using sourceBound
    have valueCanonical := canonical index sourceBound
    have sourceExact :
        @getElem! (List RawQM31) Nat RawQM31 _ _
            V7CallerCurrentReleaseR26FoldValuesPrefixSemantics.instInhabitedRawQM31
            values.val index = values.val[index]'listBound := by
      apply List.getElem!_of_getElem?
      simp [listBound]
    rw [sourceExact] at valueCanonical
    rw [prefixValExact]
    simpa [indexFour, listBound] using valueCanonical
  · funext index
    unfold terminalValues modelPrefix exactValueAt
    rw [prefixValExact]
    have listBound : index.val < values.val.length := by
      simpa [Array.length_eq] using
        (show index.val < 256 by omega)
    have takeBound : index.val < (values.val.take 4).length := by
      simp only [List.length_take]
      omega
    have terminalExact :
        @getElem! (List RawQM31) Nat RawQM31 _ _
            V7CallerCurrentReleaseR26TerminalStructuredComponents.instInhabitedRawQM31
            (values.val.take 4) index.val =
          (values.val.take 4)[index.val]'takeBound := by
      apply List.getElem!_of_getElem?
      simp [takeBound]
    have takeElemExact :
        (values.val.take 4)[index.val]'takeBound =
          values.val[index.val]'listBound := by
      rw [List.getElem_take]
    have sourceExact :
        @getElem! (List RawQM31) Nat RawQM31 _ _
            V7CallerCurrentReleaseR26K1FoldValuesPrefixBridge.instInhabitedRawQM31
            values.val index.val = values.val[index.val]'listBound := by
      apply List.getElem!_of_getElem?
      simp [listBound]
    exact congrArg
      V7CallerCurrentReleaseR26K1StructuredWeightBridge.exactRaw
      (terminalExact.trans (takeElemExact.trans sourceExact.symm))

#print axioms terminal_prefix_corresponds

end V7CallerCurrentReleaseR26TerminalPrefixSemantics
