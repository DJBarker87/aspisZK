import FJf_EbyKNew
import FJf_CommonValue
import FJc_InactiveCoefficientsModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_PartialCell
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ NE wide)

def term (f : Slice U8) (common : Array NQ 16#usize) (s : Usize) (j : Nat) : AspisWideTower.WideExact :=
  FJc_InactiveCoefficientsModel.field f (16*s.val+j)*⟨FJf_QMArray.value common j,0⟩

def sumPrefix (f : Slice U8) (common : Array NQ 16#usize) (s : Usize) : Nat → AspisWideTower.WideExact
  | 0 => 0
  | n+1 => sumPrefix f common s n+term f common s n

theorem offset (s j : Usize) (hs : s.val < 4) (hj : j.val < 16) :
    (Usize.wrapping_add (Usize.wrapping_mul 16#usize s) j).val=16*s.val+j.val := by
  have size : 4096≤UScalar.size .Usize := by
    rw [UScalar.size_def,UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h|h <;> simp [h]
  have hp : 16*s.val < UScalar.size .Usize := by omega
  have ht : 16*s.val+j.val < UScalar.size .Usize := by omega
  rw [Usize.wrapping_add_val_eq,Usize.wrapping_mul_val_eq,
    show (16#usize).val=16 from by decide,Nat.mod_eq_of_lt hp,Nat.mod_eq_of_lt ht]

theorem value (f : Slice U8) (common : Array NQ 16#usize) (s : Usize) (hs : s.val < 4)
    (hc : FJf_QMArray.canon common) (iter cursor : FIo_RangeNext.Range)
    (dot next : FIo_Native.fast_pairing.EbyKDot) (he : iter.end.val=16)
    (bound : FJf_EbyKCodec.Bound dot)
    (run : FIo_Native.weights.partial_dot_loop.body f common s iter dot=ok (.cont (cursor,next))) :
    cursor.end=iter.end ∧ cursor.start.val=iter.start.val+1 ∧ iter.start.val < iter.end.val ∧
    FJf_EbyKCodec.Bound next ∧ next.count.val=dot.count.val+1 ∧
    FJf_EbyKCodec.model next=FJf_EbyKCodec.model dot+term f common s iter.start.val := by
  unfold FIo_Native.weights.partial_dot_loop.body at run
  obtain ⟨⟨o,cursor'⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases run
  | some j =>
    simp only [lift,bind_tc_ok] at run
    obtain ⟨we,hwe,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨q,hq,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨⟨r,dot'⟩,hdot,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases r with
    | Err e => cases run
    | Ok u =>
      cases u
      cases Result.ok.inj run
      have pr := FIo_RangeNext.some_next iter cursor j hn
      have hj : j.val < 16 := by rw [pr.1];omega
      have off := offset s j hs hj
      have canonQ := hc q (List.mem_of_getElem? (FJc_ReadSlot.slot _ _ _ hq))
      have canonE := FIo_FieldCanonical.field f _ we hwe
      have push := FJf_EbyKPush.value dot next we q canonE canonQ bound hdot
      have fv := FJc_InactiveCoefficientsModel.field_read f _ we (by rw [off];omega) hwe
      have qv := FJf_QMArray.read common j q hq
      have vt : decodeWide (wide we)*FJf_EbyKCodec.scalar q=term f common s j.val := by
        unfold term FJf_EbyKCodec.scalar
        rw [off] at fv
        rw [fv,qv]
      refine ⟨pr.2.1,pr.2.2.1,pr.2.2.2,push.2.1,push.1,?_⟩
      rw [push.2.2,vt,pr.1]
#print axioms offset
#print axioms value
end AspisR1.FJf_PartialCell
end
