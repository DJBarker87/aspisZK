import PoseidonRawLimbReassembly
import RawPoseidonRowField
import ExtractedMaskQM31Exact

set_option autoImplicit false
namespace AspisR1.PoseidonExternalColumn1Reassembly
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.RawPoseidonExtensionWords
open AspisR1.RawPoseidonRowField

abbrev QM := field.QM31
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev Limbs := AspisR1.RawPoseidonExtensionWords.Limbs

def qWords (q : QM) : Fin 4 → Nat := fun j =>
  match j.val with
  | 0 => q.c0.a.val
  | 1 => q.c0.b.val
  | 2 => q.c1.a.val
  | 3 => q.c1.b.val
  | _ => 0

def sumWords (sums : Array (Array Std.U64 4#usize) 4#usize)
    (lane : Fin 4) : Fin 4 → Nat :=
  fun j =>
    let row := sums.val[lane.val]'(by simpa [sums.property] using lane.isLt)
    (row.val[j.val]'(by simpa [row.property] using j.isLt)).val

theorem qWords_decode (q : QM) : decodeWords (qWords q) = Decode q := by
  ext <;> simp [qWords, decodeWords, Decode, AspisR1.ExtractedMaskQM31Exact.decode]

theorem add_column_reassembly
    (q : QM) (sums : Array (Array Std.U64 4#usize) 4#usize) (lane : Fin 4)
    (raw : Limbs)
    (hraw : ∀ j : Fin 4,
      (AspisR1.RawPoseidonExtensionWords.limbAt raw j).val = qWords q j + sumWords sums lane j) :
    ∃ out : QM,
      state_only_poseidon.extension_from_raw_limbs raw = .ok out ∧
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM out ∧
      Decode out = Decode q + decodeWords (sumWords sums lane) := by
  obtain ⟨out,hrun,hcanon,hdecode⟩ := AspisR1.PoseidonRawLimbReassembly.source_success raw
  have hvals : (fun j : Fin 4 =>
      (AspisR1.RawPoseidonExtensionWords.limbAt raw j).val) =
      (fun j => qWords q j + sumWords sums lane j) := by
    funext j
    exact hraw j
  refine ⟨out,hrun,hcanon,?_⟩
  have hdecodeExact : Decode out = decodeWords (fun j => (AspisR1.RawPoseidonExtensionWords.limbAt raw j).val) := by
    simpa [Decode, AspisR1.PoseidonRawLimbReassembly.Decode] using hdecode
  rw [hdecodeExact, hvals, decodeWords_add, qWords_decode]

#print axioms qWords_decode
#print axioms add_column_reassembly
end AspisR1.PoseidonExternalColumn1Reassembly
