import R1Z.PV_Inv_MapGlobalStep
import R1Z.PV_Inv_GlobalSafety
set_option autoImplicit false
namespace R1Z.PV_Inv_MapGlobalRun
open PV_Inv_RawSlots PV_Inv_GlobalSlots PV_Inv_MapGlobalStep
variable {I V V' W : Type} [DecidableEq I] [Zero W] [DecidableEq W]

theorem run_map (f : V → V') (s : State I V W) (es : List (I × Entry V W)) :
    PV_Inv_GlobalSlots.run (state f s) (es.map (keyed f)) =
      (PV_Inv_GlobalSlots.run s es).map (state f) := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons,PV_Inv_GlobalSlots.run,step_map]
    cases h : PV_Inv_GlobalSlots.step s e with
    | none => rfl
    | some u => simpa only [Option.map_some,Option.bind_some] using ih u

theorem empty_map (f : V → V') (z : V) :
    state f (PV_Inv_GlobalSafety.empty (I := I) (W := W) z) = PV_Inv_GlobalSafety.empty (f z) := rfl

#print axioms run_map
#print axioms empty_map
end R1Z.PV_Inv_MapGlobalRun
