import NGO_DecodeTotal
import NGO_FirstError
import FIq_S_RawActualDecodeKMainAdapter
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_DecodePort
open AspisR1PublicPreparation.RawActualDecodeKMainAdapter
/-- Full adopted record token, with exact original borrowed framing. -/
theorem token (record : MainRecord) :
    (recordToDecoder record).row=record.row ∧
      (recordToDecoder record).framed=record.framed := ⟨rfl,rfl⟩
/-- All eleven error constructors are preserved and distinguished. -/
def errorBack : MainError → DecodeError
  | .Allocation => .Allocation
  | .RowOrder a b => .RowOrder a b
  | .InvalidRow => .InvalidRow
  | .Tag row => .Tag row
  | .Length row => .Length row
  | .NonCanonical row offset => .NonCanonical row offset
  | .Boundary round => .Boundary round
  | .Terminal => .Terminal
  | .EqualCirclePoints => .EqualCirclePoints
  | .TrailingBytes => .TrailingBytes
  | .Public => .Public

theorem error_roundtrip (e : DecodeError) : errorBack (decoderErrorToMain e)=e := by cases e <;> rfl
theorem error_reverse (e : MainError) : decoderErrorToMain (errorBack e)=e := by cases e <;> rfl

/-- Complete result transport into the installed indexed-decoder adapter,
including zero initialization and first-error unchanged suffix. There is no
accepted output premise. Original entry-read facts remain explicit. -/
theorem result (N off start size finish : Usize) (r : MainRecord) (payload window : Slice U8)
    (row : ¬r.row<14#u8)
    (offset : Usize.checked_mul off 32#usize=some start)
    (length : Usize.checked_mul N 32#usize=some size)
    (addition : Usize.checked_add start size=some finish)
    (original : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.payload (recordToDecoder r)=ok payload)
    (get : core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8)
      payload {start,«end»:=finish}=ok (some window))
    (d : NGD_DecodeTrace.Domain N (recordToDecoder r) off start) :
    ∃ final, decodeMain N r off = decoderResultToMain N
        (ok (match final.2 with | none=>.Ok final.1 | some reply=>reply)) ∧
      ∃ halt, 0≤halt ∧ halt≤N.val ∧ NGO_FirstError.Terminal d halt final ∧
        ∀ j (inside : j<N.val), halt≤j →
          final.1.val[j]'(by rw [final.1.property];exact inside) =
            (Array.repeat N AspisR1DecodeKFullV10.aspis_core.field.QM31.ZERO).val[j]'(by simp [Array.repeat];exact inside) := by
  obtain ⟨final,trace,run⟩ := NGO_DecodeTotal.ready N off start size finish
    (recordToDecoder r) payload window row offset length addition original get d
  refine ⟨final,?_,?_⟩
  · exact congrArg (decoderResultToMain N) run
  · exact NGO_FirstError.suffix d {start:=0#usize,«end»:=N}
      (Array.repeat N AspisR1DecodeKFullV10.aspis_core.field.QM31.ZERO) final trace rfl (by simp)
#print axioms token
#print axioms error_roundtrip
#print axioms error_reverse
#print axioms result
end NGO_DecodePort
