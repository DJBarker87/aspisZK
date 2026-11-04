import NGO_EntryFacts
import NGO_NativeConstruct
import NGO_QBridge
import NGO_DecodePort
import NGO_CallerDomains
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
