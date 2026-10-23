import S2I_ReturnData
import S2F_Stage2Cuts

/-! Install the runtime-interpreted clear in the actual extracted S2E callback.
This proves the reference cut under a primitive runtime premise. Native↔owned
state/ABI interpretation remains S2-H's port; no other child is installed. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2I.ClearChild
open S2E_Reference.S2E_Reference AspisR1.S2E ReturnData

def install {C A E : Type} (remaining : Children C (State A E))
    (syscall : State A E → List U8 → Result (State A E)) : Children C (State A E) :=
  {remaining with clear_return_data := clear syscall}

theorem reached_asq8 {C A E : Type} (ops : S2E_Reference.Ops)
    (remaining : Children C (State A E))
    (syscall : State A E → List U8 → Result (State A E))
    (runtime : RuntimePremise syscall) (original : Original (State A E))
    (finalState : State A E) (finalSdk : SDK)
    (accepted : stage2 ops (install remaining syscall) original.state original.sdk
      original.program original.data = ok (.Ok (),finalState,finalSdk)) :
    ∃ validatedState validated beforeDrop,
      remaining.validate_asq8 (set original.state []) original.program original.sdk original.data =
        ok (.Ok validated,validatedState) ∧
      stage2_proof ops (install remaining syscall) validatedState original.sdk validated =
        ok (.Ok (),beforeDrop,finalSdk) ∧
      remaining.drop_statement beforeDrop validated.statement = ok finalState ∧
      (set original.state []).accounts = original.state.accounts ∧
      (set original.state []).events = original.state.events ++ [.setReturnData []] := by
  obtain ⟨cleared,validatedState,validated,beforeDrop,hclear,hvalidate,hbody,hdrop⟩ :=
    S2F.stage2_prefix ops (install remaining syscall) original finalState finalSdk accepted
  have same : cleared = set original.state [] := by
    change clear syscall original.state = ok cleared at hclear
    rw [(clear_contract syscall runtime original.state).1] at hclear
    exact (Result.ok.inj hclear).symm
  subst cleared
  exact ⟨validatedState,validated,beforeDrop,hvalidate,hbody,hdrop,rfl,rfl⟩

#print axioms reached_asq8
end AspisR1.S2I.ClearChild
