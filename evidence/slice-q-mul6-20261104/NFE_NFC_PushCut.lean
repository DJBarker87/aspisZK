import NFE_NFC_TailSources
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFE_NFC_PushCut
open Aeneas Aeneas.Std Result NEV_DotCarrier NFE_NFC_TailSources

theorem actual (before after : NFE_NFC_TailTrace.Acc) (args : NE×NQ)
    (run : push before args=ok after) :
    FIo_Native.fast_pairing.EbyKDot.push before args.1 args.2=ok (.Ok (),after) := by
  unfold push at run
  obtain ⟨⟨result,next⟩,call,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  simp only [Aeneas.Std.uncurry] at run
  obtain ⟨unit,unwrap,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  cases unit
  have tag:=NFE_NFC_TailTrace.unwrap_unit result unwrap
  have same : next=after := Result.ok.inj run
  simpa only [tag,same] using call

theorem count (before after : NFE_NFC_TailTrace.Acc) (args : NE×NQ)
    (small : before.count.val<3) (run : push before args=ok after) :
    after.count.val=before.count.val+1 :=
  NFA_TailCounter.step before args.1 args.2 after small (actual before after args run)
#print axioms actual
#print axioms count
end AspisR1.NFE_NFC_PushCut
end
