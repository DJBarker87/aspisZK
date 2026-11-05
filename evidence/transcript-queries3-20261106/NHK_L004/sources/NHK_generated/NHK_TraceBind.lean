import NGQ_Cuts
import NGQ_MaterializeChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHK_TraceBind
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
abbrev Trace := NGQ_Cuts.Trace

def Continuation {A B : Type}
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (out : Result A) (k : A → Code B) (final : Result B)
    (suffix : SdkC_Source.Log) : Prop :=
  match out with
  | .ok a => Trace hashv (k a) final suffix
  | .fail error => final = .fail error ∧ suffix = []
  | .div => final = .div ∧ suffix = []

/-- Compose chronological local edges, preserving an unsuccessful call and
ending its invocation there. No independently selected final run is assumed. -/
theorem append {A B : Type}
    {hashv : SdkC_Source.Parts → Result SdkC_Source.Digest}
    {code : Code A} {out : Result A} {events : SdkC_Source.Log}
    (trace : Trace hashv code out events)
    (k : A → Code B) (final : Result B) (suffix : SdkC_Source.Log)
    (tail : Continuation hashv out k final suffix) :
    Trace hashv (CheckpointBytes5Effect.bind code k) final (events ++ suffix) := by
  induction trace with
  | done a => exact tail
  | stepOk r c b edge out events rest ih =>
    exact .stepOk r (fun x => CheckpointBytes5Effect.bind (c x) k) b edge
      final (events ++ suffix) (ih tail)
  | stepFail r c error edge =>
    obtain ⟨rfl,rfl⟩ := tail
    exact .stepFail r (fun x => CheckpointBytes5Effect.bind (c x) k) error edge
  | stepDiv r c edge =>
    obtain ⟨rfl,rfl⟩ := tail
    exact .stepDiv r (fun x => CheckpointBytes5Effect.bind (c x) k) edge
  | readOk parts c reply edge out events rest ih =>
    exact .readOk parts (fun x => CheckpointBytes5Effect.bind (c x) k) reply edge
      final (events ++ suffix) (ih tail)
  | readFail parts c error edge =>
    obtain ⟨rfl,rfl⟩ := tail
    exact .readFail parts (fun x => CheckpointBytes5Effect.bind (c x) k) error edge
  | readDiv parts c edge =>
    obtain ⟨rfl,rfl⟩ := tail
    exact .readDiv parts (fun x => CheckpointBytes5Effect.bind (c x) k) edge

#print axioms append
end AspisR1.NHK_TraceBind
end
