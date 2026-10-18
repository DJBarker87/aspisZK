import Aeneas
import PoseidonLeadingSourceDeclarationsV5
import PoseidonExternalLocalPackedCallbackSource
import RawPoseidonExternalRowReads
import ExtractedMaskTowerAdd
import PoseidonInternalStateWords

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open Aeneas Aeneas.Std Result
namespace AspisR1.PoseidonExternalLocalInputLimbsBound
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskTowerAdd
open AspisR1.RawPoseidonExternalRowReads

abbrev InputQMs := Array field.QM31 4#usize
abbrev RawInput := Array (Array U32 4#usize) 4#usize

def limbsOf (q : field.QM31) : Array U32 4#usize :=
  Array.make 4#usize [q.c0.a, q.c0.b, q.c1.a, q.c1.b]

def mappedRows (input : InputQMs) : RawInput :=
  ⟨input.val.map limbsOf, by simpa [input.property]⟩

theorem extension_limbs_map_exact (input : InputQMs) :
    core.array.Array.map (BuiltinFnMut field.QM31 (Array U32 4#usize)) input
      state_only_poseidon.extension_limbs = .ok (mappedRows input) := by
  exact AspisR1.PoseidonExternalLocalPackedCallbackSource.extension_limbs_array_map_success input

/-- A canonical QM cell contributes four canonical M31 limbs to the actual
mapped callback input. -/
theorem mapped_limb_lt_P (input : InputQMs)
    (hcanonical : ∀ i : Fin 4,
      CanonicalQM (input.val[i.val]'(by simpa [input.property] using i.isLt)))
    (r : Fin 4) (limb : Usize) (hlimb : limb.val < 4) :
    (limbValue (mappedRows input) r limb hlimb).val < P := by
  let q : field.QM31 := input.val[r.val]'(by simpa [input.property] using r.isLt)
  have hq := hcanonical r
  have hwords := AspisR1.PoseidonInternalStateWords.wordVec_canonical q hq
  have hrow : rowValue (mappedRows input) r = limbsOf q := by
    simp [rowValue, mappedRows, limbsOf, q]
  let j : Fin 4 := ⟨limb.val, hlimb⟩
  have hget := congrArg (fun row : Array U32 4#usize =>
    (row.val[limb.val]'(by simpa [row.property] using hlimb)).val) hrow
  have hbound := hwords j
  change ((limbsOf q).val[limb.val]'(by
    simpa [limbsOf] using hlimb)).val < P at hbound
  exact lt_of_eq_of_lt hget hbound

#print axioms extension_limbs_map_exact
#print axioms mapped_limb_lt_P
end AspisR1.PoseidonExternalLocalInputLimbsBound
