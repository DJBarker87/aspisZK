import RPu_FJl_TailWindow0
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_TailWindow2
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ qm)
/-- SAME second C2 tail byte window, following selected coefficient27. -/
theorem value (q : Array U8 608#usize) (slot : Usize) (hs : slot.val<4) (v : NQ)
    (run : FJi_TailInputs.read2 q slot=ok v) :
    ExactLeafFieldCodec.decodeQM31 (OraclePortCompactDraft.slice
      (MultiproofConeCanonical.bytesOf q.val) (480+32*slot.val+16) 16)=some (decodeQM (qm v)) := by
  unfold FJi_TailInputs.read2 at run
  obtain ⟨delta,hd,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨base,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨off,hoff,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨start,hstart,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨stop,hstop,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨s,range,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨o,parse,unwrap⟩ := Port3_PushFrame.bind_success _ _ _ run
  have d := FIw_WordValue.mul slot 32#usize delta hd
  have b := FIw_WordValue.add 480#usize delta base hb
  have z := FIw_WordValue.mul 1#usize 16#usize off hoff
  have a := FIw_WordValue.add base off start hstart
  have e := FIw_WordValue.add start 16#usize stop hstop
  change delta.val=slot.val*32 at d
  change base.val=480+delta.val at b
  change off.val=1*16 at z
  change stop.val=start.val+16 at e
  have startVal : start.val=480+32*slot.val+16 := by omega
  have h := FJl_QMWindow.value q start stop s o v e (by omega) range parse unwrap
  rwa [startVal] at h
#print axioms value
end AspisR1.FJl_TailWindow2
end
