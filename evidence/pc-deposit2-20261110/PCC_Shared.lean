import PCC_Reference
set_option autoImplicit false
namespace PCC
open PCA
/-- Exact nested shared-data scope: returning errors drop this guard; aborts
retain the live token. Parent liveGuards are never cleared by a child scope. -/
def withShared {α : Type} (account : Nat)
    (body : NLF_SdkModel.Payload → Reference α) : Reference α := fun s =>
  let a := NLF_ParentModel.acquire s.loans account .shared
  let acquired := {s with loans := a.1}
  let eventsBefore := [PCA_Event.token (.acquire account s.loans.next .shared a.2)]
  match a.2 with
  | .error _ => ⟨acquired,eventsBefore,.error (.program borrowFailed)⟩
  | .ok g =>
    let d := NLF_ParentModel.deref acquired.loans g
    let dereferenced := {acquired with loans := d.1}
    let eventsBefore := eventsBefore ++ [PCA_Event.token (.deref g d.2)]
    match d.2 with
    | .error _ => ⟨dereferenced,eventsBefore,.abort "invalid shared guard"⟩
    | .ok payload =>
      let r := body payload dereferenced
      match r.reply with
      | .abort reason => ⟨r.state,eventsBefore ++ r.events,.abort reason⟩
      | reply =>
        let dropped := NLF_ParentModel.release r.state.loans g
        let events := eventsBefore ++ r.events ++ [PCA_Event.token (.release g dropped.2)]
        match dropped.2 with
        | .error _ => ⟨{r.state with loans := dropped.1},events,.abort "invalid shared drop"⟩
        | .ok () => ⟨{r.state with loans := dropped.1},events,reply⟩
end PCC
