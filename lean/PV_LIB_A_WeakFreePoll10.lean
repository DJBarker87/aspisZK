import PV_LIB_A_WeakOwnerFree10
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_WeakFreePoll10
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable

def carrier (C : Carrier OWNER Data) (K : Control) (b : Bool) : Carrier OWNER Data :=
  PV_LIB_A_UnwindMatch.carrier (PV_LIB_A_DestructorValues10.carrier C b) K

/-- Exact free-poll graph on the completed ORIGINAL source carrier. Every
resource answer flows to sourceReceive. There is no unit-existence or free-
success hypothesis; allocator/backing gaps remain explicit branches. -/
theorem graph (C : Carrier OWNER Data) (K : Control) (b : Bool)
    (resources : Resources) (encode : Encode) (c : Config) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) (site : SourceSite) (p : Address) :
    PV_LIB_A_WeakOwnerFree9.poll (carrier C K b) resources encode c w es stack site p =
      match PV_LIB_A_WeakOwnerFree9.weakAllocator (carrier C K b) c w site with
      | none => PV_LIB_A_WeakOwnerFree9.gap c w es stack
      | some () => match PV_LIB_A_AllocationBacking9.deallocate resources encode w p with
        | none => PV_LIB_A_WeakOwnerFree9.gap c w es stack
        | some r => sourceReceive (carrier C K b) c es stack site (.deallocate p)
            (PV_LIB_A_WeakOwnerFree9.reply PV_LIB_A_DestructorValues10.unitValue r) := by
  have unit : (carrier C K b).aggregate PV_LIB_A_GenericDropMachine.unitTag [] =
      some PV_LIB_A_DestructorValues10.unitValue := rfl
  unfold PV_LIB_A_WeakOwnerFree9.poll
  rw [unit]
  cases PV_LIB_A_WeakOwnerFree9.weakAllocator (carrier C K b) c w site with
  | none => rfl
  | some u => cases u; rfl

/-- The exact selected last-Weak transition decrements once THEN performs that
poll on the decremented source state. This is local step composition; deriving
selection/count from the complete486/584/payload history remains separate. -/
theorem last_step (C : Carrier OWNER Data) (K : Control) (b : Bool)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : SourceSite) (p : Address) (post : Store Data)
    (selected : sourceSelect (v2ProvenancePrograms P) c = some site)
    (weak : site.action = .weakDrop683)
    (begun : PV_LIB_A_WeakDropSource.PV_THR2_LibrarySemantics_WeakDropBegin683
      (carrier C K b) site.arguments c.store w = some ⟨post,.deallocate p⟩) :
    PV_LIB_A_WeakOwnerFree10.step (PV_THR2_OwnInitExactReturnedCases.carrier C b)
      K P resources encode H values ⟨⟨⟨.running c,w,es⟩,stack⟩,none⟩ =
      PV_LIB_A_WeakOwnerFree9.poll (carrier C K b)
        resources encode {c with store := post} w es stack site p := by
  simp only [PV_LIB_A_WeakOwnerFree10.step,PV_LIB_A_WeakOwnerFree9.step,selected,weak]
  change (match PV_LIB_A_WeakDropSource.PV_THR2_LibrarySemantics_WeakDropBegin683
      (carrier C K b) site.arguments c.store w with
    | some ⟨t,.deallocate q⟩ => PV_LIB_A_WeakOwnerFree9.poll (carrier C K b)
        resources encode {c with store := t} w es stack site q
    | _ => _) = _
  rw [begun]

#print axioms carrier
#print axioms graph
#print axioms last_step
end PV_LIB_A_WeakFreePoll10
