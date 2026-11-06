import PCC_Shared
import PCC_ReferenceInvariant
set_option autoImplicit false
namespace PCC
open PCA
/-- This conditional SUPPORT theorem is not a child root: each concrete body
must discharge its invariant clause. No successful acquisition is assumed. -/
theorem shared_preserves {α : Type} (account : Nat)
    (body : NLF_SdkModel.Payload → Reference α)
    (hb : ∀ payload, Preserves (body payload)) :
    Preserves (withShared account body) := by
  intro s hs
  have ha := NLF_ParentModel.acquire_preserves s.loans account .shared hs
  cases hAcquire : (NLF_ParentModel.acquire s.loans account .shared).2 with
  | error e => simpa only [withShared,hAcquire,Invariant] using ha
  | ok g =>
    let acquired := {s with loans := (NLF_ParentModel.acquire s.loans account .shared).1}
    have hd := NLF_ParentModel.deref_invariant acquired.loans g ha
    cases hRead : (NLF_ParentModel.deref acquired.loans g).2 with
    | error e =>
      dsimp only [acquired] at hRead
      simpa only [withShared,hAcquire,hRead,Invariant] using hd
    | ok payload =>
      dsimp only [acquired] at hRead
      let dereferenced := {acquired with loans := (NLF_ParentModel.deref acquired.loans g).1}
      let r := body payload dereferenced
      have hr := hb payload dereferenced hd
      have released := NLF_ParentModel.release_preserves r.state.loans g hr
      cases hReply : r.reply with
      | abort reason =>
        dsimp only [r,dereferenced,acquired] at hReply
        simpa only [withShared,hAcquire,hRead,hReply,Invariant] using hr
      | ok x =>
        dsimp only [r,dereferenced,acquired] at hReply
        cases hDrop : (NLF_ParentModel.release r.state.loans g).2 <;>
          dsimp only [r,dereferenced,acquired] at hDrop <;>
          simpa only [withShared,hAcquire,hRead,hReply,hDrop,Invariant] using released
      | error e =>
        dsimp only [r,dereferenced,acquired] at hReply
        cases hDrop : (NLF_ParentModel.release r.state.loans g).2 <;>
          dsimp only [r,dereferenced,acquired] at hDrop <;>
          simpa only [withShared,hAcquire,hRead,hReply,hDrop,Invariant] using released
#print axioms shared_preserves
end PCC
