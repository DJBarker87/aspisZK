import NMX_R2_Semantics
import NMX_R2_AllocationSound
import NMX_BoxPostProjection
set_option autoImplicit false
noncomputable section
namespace NMX_R2_BoxActionObservation
open Aeneas Aeneas.Std Result AspisR1 NMX_OwnedPackets
/-- Full returned Box owner/payload are retained. A stop has only its prefix;
allocator internals and pure typed-heap observations are outside the row. -/
def view {T S : Type} : Result (core.result.Result (NKY_BoxAction.Owned T) NKY_BoxAction.PE × S) →
 RSL.Obs (Except RSL.ProgramError (Box T))
 | .ok (.Ok box,_) => ⟨.ret (.ok ⟨box.owner,box.value⟩),[]⟩
 | .ok (.Err e,_) => ⟨.ret (.error (NMX_R2_Carrier.error e)),[]⟩
 | .fail _ => ⟨.abort,[]⟩
 | .div => ⟨.diverge,[]⟩

/-- Local std allocation interpretation: the real allocator terminates with
an object or aborts. This is a library condition for this adapter, not a new
233 own-input clause or a parent endpoint premise. -/
theorem member {T S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S) (size : Nat)
 (r : NP6_StdModel.Reservation) (owner : Nat)
 (decoded : core.result.Result T NKY_BoxAction.PE) (env : RSL.Env)
 (allocation : (∃ post, a.allocate s size = .ok post) ∨ (∃ failure, a.allocate s size = .fail failure)) :
 NMX_R2_Semantics.boxed owner decoded env
  (view (NKY_BoxAction.run a s size r owner (.ok decoded))) := by
 cases decoded with
 | Err e => rfl
 | Ok value =>
   rcases allocation with ⟨post,returned⟩ | ⟨failure,stopped⟩
   · cases r with
     | Err e =>
       simp only [NKY_BoxAction.run,NKY_BoxAction.newBox,returned,bind_tc_ok]
       exact NMX_R2_AllocationSound.aborted (Box.mk owner value) env
     | Ok unit =>
       cases unit
       simp only [NKY_BoxAction.run,NKY_BoxAction.newBox,returned,bind_tc_ok]
       exact NMX_R2_AllocationSound.returned (Box.mk owner value) env
   · rw [NKY_BoxAction.allocator_failure a s size r owner value failure stopped]
     exact NMX_R2_AllocationSound.aborted (Box.mk owner value) env
#print axioms member
end NMX_R2_BoxActionObservation
end
