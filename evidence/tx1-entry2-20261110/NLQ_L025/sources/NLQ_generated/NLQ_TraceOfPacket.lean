import NLQ_RowSpec094
import NHZ_NativeAssociation
set_option autoImplicit false
noncomputable section
namespace NLQ_TraceOfPacket
open Aeneas Aeneas.Std Result AspisR1 CheckpointBytes5Effect
/-- Evaluator completeness is only algebra. It creates no native packet.
Used to consume the SAME observation already certified by the child's packet. -/
theorem total {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (code : Code A) : ∃ out log, NGQ_Cuts.Trace hashv code out log := by
 induction code with
 | done a => exact ⟨.ok a,[],.done a⟩
 | @step B r k ih =>
   cases r with
   | ok b =>
     rcases ih b with ⟨out,log,tr⟩
     exact ⟨out,log,.stepOk _ _ b rfl _ _ tr⟩
   | fail e => exact ⟨.fail e,[],.stepFail _ _ e rfl⟩
   | div => exact ⟨.div,[],.stepDiv _ _ rfl⟩
 | read parts k ih =>
   cases h : hashv parts with
   | ok d =>
     rcases ih d with ⟨out,log,tr⟩
     exact ⟨out,⟨parts,.ok d⟩::log,.readOk _ _ d h _ _ tr⟩
   | fail e => exact ⟨.fail e,[⟨parts,.fail e⟩],.readFail _ _ e h⟩
   | div => exact ⟨.div,[⟨parts,.div⟩],.readDiv _ _ h⟩
/-- No inverse association of unrelated logs: `associated` is precisely the
already-certified child observation, at its SAME arguments. -/
theorem child {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (code : Code A) (observed : NGP_L181.Observation A)
 (associated : NGP_L181.NativeAssociation hashv code observed) :
 NHZ_DRIVER.Cuts hashv code observed.result observed.attempted := by
 obtain ⟨out,log,tr⟩ := total hashv code
 have hr : SdkC_Source.run hashv code [] = (out,log) := by
   simpa only [List.nil_append] using NGQ_Cuts.run tr []
 have eq : (observed.result,observed.attempted)=(out,log) := associated.trans hr
 have ho := congrArg Prod.fst eq
 have hl := congrArg Prod.snd eq
 change observed.result=out at ho
 change observed.attempted=log at hl
 rw [ho,hl]
 exact .leaf tr
#print axioms total
#print axioms child
end NLQ_TraceOfPacket
