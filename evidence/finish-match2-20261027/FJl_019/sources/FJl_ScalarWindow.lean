import FJi_DecodeM31
import FIw_WordValue
import FJc_ReadSlot
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_ScalarWindow
open Aeneas Aeneas.Std Result
/-- Expose the four SAME bytes of a successful scalar read, before relating
them to any literal word. Arithmetic is inverted symbolically. -/
theorem reached (q : Array U8 608#usize) (slot term : Usize) (v : U32)
    (run : JFr_TX2_ScalarRead.read q slot term=ok v) :
    ∃ (start stop : Usize) (s : Slice U8) (a : Array U8 4#usize),
      start.val=slot.val*120+term.val*4 ∧ stop.val=start.val+4 ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice U8)) q {start,«end»:=stop}=ok s ∧
      core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s=ok (.Ok a) ∧
      FIp_DotDecode.field.M31.from_le_bytes a=ok (some v) ∧ v=core.num.U32.from_le_bytes a := by
  unfold JFr_TX2_ScalarRead.read at run
  obtain ⟨base,hbase,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨delta,hdelta,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨start,hs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨start1,hs1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same := Result.ok.inj (hs.symm.trans hs1)
  subst start1
  obtain ⟨stop,he,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨s,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨r,hcopy,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases r with
  | Err e => cases run
  | Ok a =>
    simp only [core.result.Result.unwrap,bind_tc_ok] at run
    obtain ⟨o,hd,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases o with
    | none => cases run
    | some x =>
      cases Result.ok.inj run
      have hb := FIw_WordValue.mul slot 120#usize base hbase
      have hdelt := FIw_WordValue.mul term 4#usize delta hdelta
      have hstart := FIw_WordValue.add base delta start hs
      have hstop := FIw_WordValue.add start 4#usize stop he
      exact ⟨start,stop,s,a,by simpa only [hb,hdelt] using hstart,hstop,hr,hcopy,hd,
        (FJi_DecodeM31.value a v hd).1⟩
#print axioms reached
end AspisR1.FJl_ScalarWindow
end
