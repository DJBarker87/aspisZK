import PV_LIB_SPEC_LaneA_View
set_option autoImplicit false
namespace PV_LIB
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- Public row observations. Internal source-machine diagnostics may retain a
Store at abort; that Store and the backend world never cross this interface. -/
inductive MachineObservation (W E : Type) where
  | state : PV_THR2_IntrinsicState.State W E → MachineObservation W E
  | abort : List E → MachineObservation W E

def observe {W E : Type} (q : PV_THR2_IntrinsicState.State W E) : MachineObservation W E :=
  match q.current.status with
  | .fault .abort _ => .abort q.current.events
  | _ => .state (view q)

theorem abort_prefix {W E : Type} (s : Store Data) (w : W) (es : List E) (stack : List Config) :
    observe (⟨⟨.fault .abort s,w,es⟩,stack⟩ : PV_THR2_IntrinsicState.State W E) =
      MachineObservation.abort es := rfl

theorem observe_view {W E : Type} (q : PV_THR2_IntrinsicState.State W E) :
    observe (view q) = observe q := by
  cases q with
  | mk current suspended =>
    cases current with
    | mk status world events =>
      cases status with
      | running c => simp [observe,view,statusView,configView,storeView,List.map_map,Function.comp_def]
      | returned r s => simp [observe,view,statusView,configView,storeView,List.map_map,Function.comp_def]
      | undefined a s => simp [observe,view,statusView,configView,storeView,List.map_map,Function.comp_def]
      | fault f s => cases f <;> simp [observe,view,statusView,configView,storeView,List.map_map,Function.comp_def]

#print axioms abort_prefix
#print axioms observe_view
end PV_LIB
