import NLV_RunLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_EvalTrace
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
/-- Source evaluation always supplies a chronological source trace. This is
NOT existence of a native invocation or of physical Cut admission. -/
theorem exists_trace {A : Type} (h : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (c : Code A) : ∃ out log, NGQ_Cuts.Trace h c out log := by
 induction c with
 | done a => exact ⟨ok a,[],.done a⟩
 | step r k ih =>
   cases r with
   | ok a => obtain ⟨out,log,tail⟩:=ih a;exact ⟨out,log,.stepOk _ _ a rfl _ _ tail⟩
   | fail e => exact ⟨fail e,[],.stepFail _ _ e rfl⟩
   | div => exact ⟨div,[],.stepDiv _ _ rfl⟩
 | read parts k ih =>
   cases edge : h parts with
   | ok a => obtain ⟨out,log,tail⟩:=ih a;exact ⟨out,⟨parts,ok a⟩::log,.readOk parts k a edge out log tail⟩
   | fail e => exact ⟨fail e,[⟨parts,fail e⟩],.readFail parts k e edge⟩
   | div => exact ⟨div,[⟨parts,div⟩],.readDiv parts k edge⟩
theorem of_run {A : Type} (h : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (c : Code A) (out : Result A) (log : SdkC_Source.Log)
 (equal : SdkC_Source.run h c []=(out,log)) : NGQ_Cuts.Trace h c out log := by
 obtain ⟨actual,events,trace⟩:=exists_trace h c
 have eval:=NGQ_Cuts.run trace []
 simp only [List.nil_append] at eval
 have same:=(eval.symm.trans equal)
 cases same
 exact trace
#print axioms exists_trace
#print axioms of_run
end AspisR1.NLV_EvalTrace
end
