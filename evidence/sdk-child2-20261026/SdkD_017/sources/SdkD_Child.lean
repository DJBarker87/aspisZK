import SdkD_FirstChild
import SdkD_Second
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_Child
open Aeneas Aeneas.Std Result
open S2W_ExpandedChildren

/-- Site-only projection of the literal child execution. Oracle reads are not
claimed to be absent; their separate global experiment remains to instantiate. -/
def expand {A : Type} (r : Result (A × List S2LeadInterface.Site)) :
    Result (A × List (S2W_ExpandedTrace.Event Unit)) :=
  match r with
  | .ok pair => .ok (pair.1,pair.2.map .site)
  | .fail e => .fail e
  | .div => .div

def execute {F : Type} (adapter : AdapterRw.Ops) (current : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    {A : Type} (call : S2W_Trace.Call A) : Result (A × List (S2W_ExpandedTrace.Event Unit)) :=
  let sdk := ClaimsUnrolledSdk.sdkOps (Tx2I_Install.install adapter stage finish) current B std
  match call with
  | .op10 D semantic pub proof split hash obs => expand
      (SdkD_FirstChild.execute (RowShape_InstalledSlots.verifierOps current B std)
        D semantic pub proof split hash obs)
  | .op11 D pub proof checkpoint hash obs => expand
      (SdkD_Second.execute (Tx2I_Install.stage stage finish) D pub proof checkpoint hash obs)
  | other => S2W_Trace.thenResult (S2W_Trace.invoke sdk other) (fun value => .ok (value,[]))

theorem expand_erasure {A : Type} (r : Result (A × List S2LeadInterface.Site)) :
    S2W_Trace.thenResult (expand r) (fun pair => .ok pair.1) =
      S2W_Trace.thenResult r (fun pair => .ok pair.1) := by cases r <;> rfl

theorem erasure {F : Type} (adapter : AdapterRw.Ops) (current : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    {A : Type} (call : S2W_Trace.Call A) :
    S2W_Trace.thenResult (execute adapter current stage finish B std call) (fun pair => .ok pair.1) =
      S2W_Trace.invoke
        (ClaimsUnrolledSdk.sdkOps (Tx2I_Install.install adapter stage finish) current B std) call := by
  cases call <;> simp only [execute]
  all_goals first
    | (rw [expand_erasure]; exact SdkD_FirstChild.erasure _ _ _ _ _ _ _ _)
    | (rw [expand_erasure]; exact SdkD_Second.erasure _ _ _ _ _ _ _)
    | (generalize S2W_Trace.invoke _ _ = r; cases r <;> rfl)

def port {F : Type} (adapter : AdapterRw.Ops) (current : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    ChildConeJoin Unit (ClaimsUnrolledSdk.sdkOps (Tx2I_Install.install adapter stage finish) current B std) :=
  ⟨execute adapter current stage finish B std,erasure adapter current stage finish B std⟩

#print axioms expand_erasure
#print axioms erasure
end AspisR1.SdkD_Child
end
