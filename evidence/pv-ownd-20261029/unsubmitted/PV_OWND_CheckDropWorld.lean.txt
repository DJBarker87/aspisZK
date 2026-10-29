import R1Z.PV_OWND_CheckResult
import R1Z.PV_OWND_InitialDrop
set_option autoImplicit false
namespace R1Z.PV_OWND_CheckDropWorld
open PV_OWN_Heap PV_OWN_Operations PV_OWNC_Vector PV_OWN_Link PV_W_Threading PV_OWND_InitialCheck
/-- Every destructor primitive outcome retains its cleanup post-world and call
prefix. Only successful cleanup returns the original source Result error. -/
theorem complete {S X E : Type}
 (dealloc : Nat → Request → S → Outcome E Unit × S) (error : CheckError → E)
 (b : Buffer Link) (w : State S X) (e : CheckError) (h:checks b=.error e) :
 finish dealloc error b w=
 let cleanup:=dropOwned b.owner (fun _=>dropVecPod dealloc b.token b.cell) w
 ⟨(match cleanup.outcome with
  | .ok () => .fail (error e)
  | .fail f => .fail f
  | .div => .div),cleanup.world,cleanup.calls⟩ := by
 rw [PV_OWND_CheckResult.error_cleanup dealloc error b w e h]
 unfold PV_W_Threading.bind
 cases hc:(dropOwned b.owner (fun _=>dropVecPod dealloc b.token b.cell) w).outcome with
 | ok unit => cases unit; simp only [lift,List.append_nil]
 | fail f => rfl
 | div => rfl
#print axioms complete
end R1Z.PV_OWND_CheckDropWorld
