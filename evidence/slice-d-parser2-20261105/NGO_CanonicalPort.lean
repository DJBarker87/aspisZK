import NGO_DecodeTotal
import NGO_FirstError
import NGO_QAssociation
import NGO_EntryFacts
import NGO_NativeConstruct
import NGO_QBridge
import NGO_CallerDomains
import RPu_FIq_S_RawActualDecodeKMainAdapter

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
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_ZeroLaw
def mainZero : AspisR1PublicPreparation.aspis_core.field.QM31 :=
  ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
open AspisR1DecodeKFullV10
/-- The emitted zero array has the exact native initializer at every index. -/
theorem initial (N : Usize) (i : Nat) (live : i<N.val) :
    (Array.repeat N aspis_core.field.QM31.ZERO).val[i]'(by
      rw [(Array.repeat N aspis_core.field.QM31.ZERO).property];exact live)=
        aspis_core.field.QM31.ZERO := by simp [Array.repeat]
/-- Literal carrier transport preserves the zero initializer for every N. -/
theorem port (N : Usize) :
    AspisR1PublicPreparation.RawActualDecodeKMainAdapter.decoderArrayToMain
      (Array.repeat N aspis_core.field.QM31.ZERO)=
        Array.repeat N mainZero := by
  apply Subtype.ext
  simp [AspisR1PublicPreparation.RawActualDecodeKMainAdapter.decoderArrayToMain,
    AspisR1PublicPreparation.RawActualDecodeKMainAdapter.decoderQMToMain,Array.repeat,aspis_core.field.QM31.ZERO,mainZero]
#print axioms initial
#print axioms port
end NGO_ZeroLaw
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_DecodeComposed
open AspisR1PublicPreparation.RawActualDecodeKMainAdapter
/-- Native schedule, full emitted result and adopted result are one constructed
execution witness on the original record. Only root input-domain facts remain;
no successful decode, source Trace, native Run or callee equality is assumed. -/
theorem result (N off : Usize) (record : MainRecord)
    (call : NGO_CallerDomains.Call record.row.val N.val off.val)
    (framed : record.framed.val.length=5+NFU_PacketDomains.payloadSize record.row.val) :
    ∃ (start : Usize) (d : NGD_DecodeTrace.Domain N (recordToDecoder record) off start)
      (window : Slice U8) (ce : core.slice.iter.ChunksExact U8) (final : NGD_DecodeTrace.Final N),
      window.val=((record.framed.val.drop 5).drop (32*off.val)).take (32*N.val) ∧
      core.slice.Slice.chunks_exact window 32#usize=ok ce ∧
      NGO_NativeTrace.Run d (NGO_ScheduleState.state ce 0#usize)
        (Array.repeat N AspisR1DecodeKFullV10.aspis_core.field.QM31.ZERO) final ∧
      decodeMain N record off=decoderResultToMain N
        (ok (match final.2 with | none=>.Ok final.1 | some reply=>reply)) ∧
      ∃ halt, halt≤N.val ∧ NGO_FirstError.Terminal d halt final ∧
        ∀ j (inside : j<N.val), halt≤j →
          final.1.val[j]'(by rw [final.1.property];exact inside) =
            (Array.repeat N AspisR1DecodeKFullV10.aspis_core.field.QM31.ZERO).val[j]'(by simp [Array.repeat];exact inside) := by
  have numbers := NGO_CallerDomains.numeric record.row.val N.val off.val call
  let start : Usize := UScalar.ofNat (32*off.val) (by scalar_tac)
  have startValue : start.val=32*off.val := rfl
  obtain ⟨d,row⟩ := NGO_CallerDomains.record_domain N off start
    (recordToDecoder record) call framed startValue
  obtain ⟨size,finish,payload,window,offset,length,addition,original,get,same⟩ := NGO_EntryFacts.construct d
  obtain ⟨ce,final,chunks,enumerate,trace,native⟩ := NGO_NativeConstruct.construct d window same
  have run := NGD_DecodeEntry.ready N off start size finish (recordToDecoder record)
    payload window row offset length addition original get d final trace
  obtain ⟨halt,low,high,terminal,frame⟩ := NGO_FirstError.suffix d
    {start:=0#usize,«end»:=N} (Array.repeat N AspisR1DecodeKFullV10.aspis_core.field.QM31.ZERO)
    final trace rfl (by simp)
  exact ⟨start,d,window,ce,final,same,chunks,native,congrArg (decoderResultToMain N) run,
    halt,high,terminal,frame⟩
#print axioms result
end NGO_DecodeComposed
