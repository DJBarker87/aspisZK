import R1Z.PV_Inv_MapSlots
import R1Z.PV_Inv_GlobalSlots
set_option autoImplicit false
namespace R1Z.PV_Inv_MapGlobalStep
open PV_Inv_RawSlots PV_Inv_GlobalSlots
variable {I V V' W : Type} [DecidableEq I] [Zero W] [DecidableEq W]

def keyed (f : V → V') (e : I × Entry V W) : I × Entry V' W := (e.1,PV_Inv_MapSlots.entry f e.2)
def state (f : V → V') (s : State I V W) : State I V' W := fun k => PV_Inv_MapSlots.slots f (s k)

theorem update_map (f : V → V') (s : State I V W) (k : I) (v : Slots V W) :
    state f (Function.update s k v) = Function.update (state f s) k (PV_Inv_MapSlots.slots f v) := by
  funext j
  by_cases h : j=k
  · subst j; simp [state]
  · simp [state,h]

theorem step_map (f : V → V') (s : State I V W) (e : I × Entry V W) :
    PV_Inv_GlobalSlots.step (state f s) (keyed f e) =
      (PV_Inv_GlobalSlots.step s e).map (state f) := by
  unfold PV_Inv_GlobalSlots.step
  rw [show PV_Inv_RawSlots.step ((state f s) (keyed f e).1) (keyed f e).2 =
    (PV_Inv_RawSlots.step (s e.1) e.2).map (PV_Inv_MapSlots.slots f) from PV_Inv_MapSlots.step_map f (s e.1) e.2]
  cases h : PV_Inv_RawSlots.step (s e.1) e.2 with
  | none => rfl
  | some v => simp only [Option.map_some]; exact congrArg some (update_map f s e.1 v).symm

#print axioms update_map
#print axioms step_map
end R1Z.PV_Inv_MapGlobalStep
