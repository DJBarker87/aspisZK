import Uni_SecondMarks
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_Second
open Aeneas Aeneas.Std Result

def sites (log : VTop_Trace.Log) : List S2LeadInterface.Site := Uni_SecondMarks.sourceSites log

def execute (ops : VTop_Stages.Ops) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (pub proof checkpoint : Slice U8)
    (hash : Hash) (obs : Option (VTop_Stages.verifier.Phase → Result Unit)) :
    Result (core.result.Result Unit VTop_Stages.verifier.Error × List S2LeadInterface.Site) :=
  VTop_Trace.thenResult
    (VTop_Trace.run ops (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof checkpoint hash obs) [])
    (fun answer => .ok (answer.1,sites answer.2))

theorem erasure (ops : VTop_Stages.Ops) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (pub proof checkpoint : Slice U8)
    (hash : Hash) (obs : Option (VTop_Stages.verifier.Phase → Result Unit)) :
    S2W_Trace.thenResult (execute ops D pub proof checkpoint hash obs) (fun answer => .ok answer.1) =
      VTop_Stages.verifier.candidate.tx2_authenticated ops D pub proof checkpoint hash obs := by
  have erase := VTop_Trace.erase_run ops
    (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof checkpoint hash obs) []
  rw [VTop_Erasure.tx2_authenticated_erasure] at erase
  generalize h : VTop_Trace.run ops
    (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof checkpoint hash obs) [] = r at erase
  unfold execute
  rw [h]
  cases r <;> exact erase

theorem accepted (ops : VTop_Stages.Ops) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (pub proof checkpoint : Slice U8)
    (hash : Hash) (obs : Option (VTop_Stages.verifier.Phase → Result Unit))
    (success : VTop_Stages.verifier.candidate.tx2_authenticated ops D pub proof checkpoint hash obs = .ok (.Ok ())) :
    execute ops D pub proof checkpoint hash obs = .ok (.Ok (),[.resume,.batch1,.query1,.finish]) := by
  obtain ⟨log,run,marks⟩ := Uni_SecondMarks.accepted_source_marks ops D hash pub proof checkpoint obs success
  simp only [execute,run,VTop_Trace.thenResult,sites,marks]

#print axioms erasure
#print axioms accepted
end AspisR1.SdkD_Second
end
