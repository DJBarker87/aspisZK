import FJj_QMSlice
import FJf_PartialCell
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_ByteDotCell
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ NE wide)

def term (f : Slice U8) (scratch : Slice NQ) (j : Nat) : OraclePortCheckpointAbiC5.E :=
  FJc_InactiveCoefficientsModel.field f j*
    algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E (FJj_QMSlice.value scratch j)

def sumPrefix (f : Slice U8) (scratch : Slice NQ) : Nat → OraclePortCheckpointAbiC5.E
  | 0=>0
  | n+1=>sumPrefix f scratch n+term f scratch n

theorem value (f : Slice U8) (scratch : Slice NQ) (hc : FJj_QMSlice.canon scratch)
    (iter cursor : FIo_RangeNext.Range) (dot next : FIo_Native.fast_pairing.EbyKDot)
    (he : iter.end.val=64) (bound : FJf_EbyKCodec.Bound dot)
    (run : FIo_Native.weights.push_byte_products_loop.body f scratch iter dot=ok (.cont (cursor,next))) :
    cursor.end=iter.end ∧ cursor.start.val=iter.start.val+1 ∧ iter.start.val < iter.end.val ∧
    FJf_EbyKCodec.Bound next ∧ next.count.val=dot.count.val+1 ∧
      FJf_EbyKCodec.model next=FJf_EbyKCodec.model dot+term f scratch iter.start.val := by
  unfold FIo_Native.weights.push_byte_products_loop.body at run
  obtain ⟨⟨o,cursor'⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none => cases run
  | some j =>
    obtain ⟨we,hwe,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨q,hq,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨⟨r,dot'⟩,hdot,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases r with
    | Err e => cases run
    | Ok u =>
      cases u
      cases Result.ok.inj run
      have pr := FIo_RangeNext.some_next iter cursor j hn
      have hj : j.val<64 := by rw [pr.1];omega
      have cq := FJj_QMSlice.canonical_read scratch j q hc hq
      have ce := FIo_FieldCanonical.field f j we hwe
      have push := FJf_EbyKPush.value dot next we q ce cq bound hdot
      have fv := FJc_InactiveCoefficientsModel.field_read f j we hj hwe
      have qv := FJj_QMSlice.read scratch j q hq
      have tv : decodeWide (wide we)*FJf_EbyKCodec.scalar q=term f scratch j.val := by
        unfold term FJf_EbyKCodec.scalar
        rw [fv,qv]
        rfl
      refine ⟨pr.2.1,pr.2.2.1,pr.2.2.2,push.2.1,push.1,?_⟩
      rw [push.2.2,tv,pr.1]
#print axioms value
end AspisR1.FJj_ByteDotCell
end
