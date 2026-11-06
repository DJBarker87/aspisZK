import PCC_Reference
import PCA_Borrow
set_option autoImplicit false
namespace PCC
open PCA
/-- Parent-owned acquisition, with no operation dictionary. -/
def acquireExclusive (site account : Nat) : Reference NLF_RefCell.Guard := fun s =>
  let r := NLF_ParentModel.acquire s.loans account .exclusive
  let s' := {s with loans := r.1}
  let event := PCA_Event.token (.acquire account s.loans.next .exclusive r.2)
  match r.2 with
  | .ok g => ⟨{s' with liveGuards := g :: s.liveGuards},[event],.ok g⟩
  | .error _ => ⟨s',[event,.propagate site borrowFailed],.error borrowFailed⟩

/-- Model-step reuse only, never a claim about the native body. -/
theorem acquire_pilot_step (site account : Nat) (k : Children) (s : PCA_State) :
    acquireExclusive site account s = (Plan.acquire site account).run k s := rfl
#print axioms acquire_pilot_step
end PCC
