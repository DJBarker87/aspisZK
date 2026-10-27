import FJl_QMWindow
import FJl_TailReads
import FIw_WordValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_TailWindow0
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ qm)
/-- SAME C1 tail byte window, on any actual slot below four. -/
theorem value (q : Array U8 608#usize) (slot : Usize) (hs : slot.val<4) (v : NQ)
    (run : FJi_TailInputs.read0 q slot=ok v) :
    ExactLeafFieldCodec.decodeQM31 (OraclePortCompactDraft.slice
      (MultiproofConeCanonical.bytesOf q.val) (120*slot.val+104) 16)=some (decodeQM (qm v)) := by
  unfold FJi_TailInputs.read0 at run
  obtain ⟨base,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨start,hstart,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨stop,hstop,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨s,range,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨o,parse,unwrap⟩ := Port3_PushFrame.bind_success _ _ _ run
  have b := FIw_WordValue.mul slot 120#usize base hb
  have a := FIw_WordValue.add base 104#usize start hstart
  have e := FIw_WordValue.add base 120#usize stop hstop
  change base.val=slot.val*120 at b
  change start.val=base.val+104 at a
  change stop.val=base.val+120 at e
  have startVal : start.val=120*slot.val+104 := by omega
  have h := FJl_QMWindow.value q start stop s o v (by omega) (by omega) range parse unwrap
  rwa [startVal] at h
#print axioms value
end AspisR1.FJl_TailWindow0
end
