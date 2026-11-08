import PV_LIB_SPEC_ActiveCells20
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ActiveCallback20
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued)
open PV_LIB_SPEC_EntryWorld18 (Entry)
open PV_LIB_A_F5FullEntry16 (activation parents closure)
open PV_LIB_SPEC_ActiveForward20 (store176 handler)
open PV_LIB_SPEC_ActiveAdoption19 (history)
open PV_LIB_SPEC_F1Arithmetic14 (stage)
open PV_LIB_SPEC_TlsNative15 (reference)

theorem dereference (p : Parameters) (w : OWNER) :
    (runtime p).carrier.dereference w reference = some PV_LIB_SPEC_Entry13.slot.source :=
  (PV_LIB_SPEC_Tls279Values16.fields p w PV_LIB_SPEC_Entry13.slot.source).2.2

def at185 (e : Entry) (a : Nat) : Execution :=
  PV_LIB_SPEC_SourceTransport15.advance PV_LIB_SPEC_ReachedEnvironment14.parameters handler 9
    (stage store176 activation parents (PV_THR2_F170.live.body.drop 31) e.world []
      (history e a 176).issued (history e a 176).consumed)

theorem original185 (e : Entry) (a : Nat) : history e a 185 = at185 e a := by
  apply PV_LIB_SPEC_HistoryExtend20.full e a 176 9
    (stage store176 activation parents (PV_THR2_F170.live.body.drop 31) e.world [] [] []).state
    (fun issued consumed => PV_LIB_SPEC_SourceTransport15.advance
      PV_LIB_SPEC_ReachedEnvironment14.parameters handler 9
      (stage store176 activation parents (PV_THR2_F170.live.body.drop 31) e.world [] issued consumed))
    (PV_LIB_SPEC_ActiveForward20.state176 e a)
  intro issued consumed
  exact PV_LIB_SPEC_ActiveTrace20.run _ _ handler _ _
    (PV_LIB_SPEC_TlsCallable16.trace _ _ handler store176 activation parents e.world [] issued consumed
      closure reference PV_LIB_SPEC_Entry13.slot.source PV_LIB_SPEC_ActiveCells20.callable176
      PV_LIB_SPEC_ActiveCells20.reference176 (dereference _ e.world))

theorem state185 (e : Entry) (a : Nat) :
    (history e a 185).state = PV_LIB_A_F5CallbackTrap16.waiting store176 activation parents
      PV_LIB_SPEC_Entry13.slot.source e.world [] := by
  rw [original185]
  unfold at185
  rw [PV_LIB_SPEC_SourceProjection15.state]
  exact PV_LIB_SPEC_TlsCallableLift16.source _ handler store176 activation parents closure reference
    PV_LIB_SPEC_Entry13.slot.source e.world [] PV_LIB_SPEC_ActiveCells20.callable176
    PV_LIB_SPEC_ActiveCells20.reference176 (dereference _ e.world)

theorem issued185 (e : Entry) (a : Nat) :
    (history e a 185).issued =
      (⟨PV_LIB_SPEC_TlsCallableHistory16.site,activation,
        PV_LIB_A_F5ClosurePending16.request store176.nextActivation PV_LIB_SPEC_Entry13.slot.source⟩ : Issued) ::
        (history e a 176).issued := by
  rw [original185]
  exact PV_LIB_SPEC_TlsCallableHistory16.issued
    (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame e a)) _ handler store176 activation parents e.world []
    (history e a 176).issued (history e a 176).consumed closure reference PV_LIB_SPEC_Entry13.slot.source
    PV_LIB_SPEC_ActiveCells20.callable176 PV_LIB_SPEC_ActiveCells20.reference176 (dereference _ e.world)

theorem consumed185 (e : Entry) (a : Nat) :
    (history e a 185).consumed = (history e a 176).consumed := by
  rw [original185]
  exact PV_LIB_SPEC_Tls279History16.consumed _ handler 9 _

#print axioms dereference
#print axioms at185
#print axioms original185
#print axioms state185
#print axioms issued185
#print axioms consumed185
end PV_LIB_SPEC_ActiveCallback20
