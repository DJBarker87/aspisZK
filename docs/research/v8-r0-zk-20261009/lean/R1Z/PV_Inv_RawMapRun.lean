import R1Z.PV_Inv_RawMap
import R1Z.PV_Inv_RawRun
set_option autoImplicit false
namespace R1Z.PV_Inv_RawMapRun
open PV_Inv_RawSlots PV_Inv_RawRun PV_Inv_RawMap
variable {V U W : Type} [Zero W] [DecidableEq W]

theorem run_map (f : V → U) (s : Slots V W) (es : List (Entry V W)) :
    run (slots f s) (es.map (entry f)) = (run s es).map (slots f) := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons,run,step_map]
    cases hs : step s e with
    | none => simp [hs]
    | some t => simp [hs,ih]

#print axioms run_map
end R1Z.PV_Inv_RawMapRun
