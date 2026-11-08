import PV_LIB_A_F170Return16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_HistoryExtend16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

/-- Composition only. Every caller below must discharge the earlier cut from
original85 and the local segment by name; this is not a join inhabitant. -/
theorem extend (e : PV_LIB_SPEC_EntryWorld18.Entry) (activation n delta : Nat)
    (s : Store Data) (a : Nat) (parents : List Frame) (body : List PV_STX2_SliceSyntax.Node)
    (out : State)
    (reached : (PV_LIB_SPEC_LaneAJoins18.history e activation n).state =
      (stage s a parents body e.world [] [] []).state)
    (segment : ∀ issued consumed,
      (PV_LIB_SPEC_ReachedNative14.run
        (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame e activation))
        PV_LIB_SPEC_ReachedEnvironment14.parameters delta
        (stage s a parents body e.world [] issued consumed)).state = out) :
    (PV_LIB_SPEC_LaneAJoins18.history e activation (n+delta)).state = out := by
  let cut := PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame e activation)
  let q := PV_LIB_SPEC_LaneAJoins18.history e activation n
  have hq : q = stage s a parents body e.world [] q.issued q.consumed := by
    apply PV_LIB_A_F170Return16.execution_ext
    · simpa only [stage] using reached
    · simp only [stage]
    · simp only [stage]
  change (PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters (n+delta)
    (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input e.world))).state = _
  rw [PV_LIB_SPEC_Original14.run_add]
  change (PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters delta q).state = _
  rw [hq]
  exact segment q.issued q.consumed

#print axioms extend
end PV_LIB_A_HistoryExtend16
