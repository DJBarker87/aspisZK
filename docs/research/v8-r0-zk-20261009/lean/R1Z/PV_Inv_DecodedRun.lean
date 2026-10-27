import R1Z.PV_Inv_MapGlobalRun
set_option autoImplicit false
namespace R1Z.PV_Inv_DecodedRun
open PV_Inv_RawSlots PV_Inv_GlobalSlots PV_Inv_MapGlobalStep PV_Inv_GlobalSafety
variable {I V V' W : Type} [DecidableEq I] [Zero W] [DecidableEq W]

theorem source_equation (f : V → V') (z : V) (z' : V') (zero_join : f z=z')
    (es : List (I × Entry V W)) (model : List (I × Entry V' W))
    (entry_join : es.map (keyed f)=model) (s : State I V W)
    (run : PV_Inv_GlobalSlots.run (empty z) es=some s) :
    PV_Inv_GlobalSlots.run (empty z') model=some (state f s) := by
  have h := PV_Inv_MapGlobalRun.run_map f (empty z) es
  rw [run,Option.map_some,PV_Inv_MapGlobalRun.empty_map,zero_join,entry_join] at h
  exact h

#print axioms source_equation
end R1Z.PV_Inv_DecodedRun
