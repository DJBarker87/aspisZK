import PV_LIB_A_ActiveDelivery17
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace PV_LIB_A_ActivePure27717
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)
open PV_LIB_SPEC_Tls277Native15 (token pointer value)

def config (s : Store Data) (a : Nat) (parents : List Frame) (p : Address) : Config :=
  PV_THR2_RunTlsNext.pending s a parents (pointer p)
def wait (s : Store Data) (p : Address) : PV_STX2_Native.Waiting Data :=
  ⟨.child token s.nextActivation [pointer p],.child s.nextActivation (.local 6),[]⟩
def returned (s : Store Data) (a : Nat) (p : Address) : Store Data :=
  write (write (config s a [] p).store ⟨s.nextActivation,0,[]⟩ (some (value p))) ⟨a,6,[]⟩ (some (value p))

theorem quiet (s : Store Data) (a : Nat) (parents : List Frame) (p : Address) (w : OWNER) :
    PV_LIB_SPEC_SourceTransport15.Quiet ⟨⟨.running (config s a parents p),w,[]⟩,[]⟩ := by
  have lookup : PV_LIB_SPEC_Full.programs PV_THR2_RunTlsNext.callee = none := rfl
  have table : PV_LIB_StoreActionTable.v2 PV_THR2_RunTlsNext.callee = none := rfl
  have head : PV_THR2_F170.live.body.drop 17 = PV_THR2_F170.node17 :: PV_THR2_F170.live.body.drop 18 := rfl
  simp [PV_LIB_SPEC_SourceTransport15.Quiet,PV_LIB_StoreActionTable.Neutral,PV_LIB_StoreActionTable.select,
    config,PV_THR2_RunTlsNext.pending,
    PV_THR2_OwnInitAction.selected,PV_THR2_OperatorAction.selected,PV_THR2_OperatorAction.instruction,
    PV_THR2_OwnUniformNeutral.configuration,PV_THR2_OwnUniformNeutral.instruction,
    head,PV_THR2_F170.node17,lookup,table]

theorem consume (cut : PV_LIB_SPEC_ReachedNative14.Cut) (s : Store Data) (a : Nat)
    (parents : List Frame) (p : Address) (w : OWNER) (issued : List Issued) (consumed : List Context) :
    (PV_LIB_SPEC_ReachedNative14.step cut PV_LIB_SPEC_ReachedEnvironment14.parameters
      (PV_LIB_SPEC_Tls277Request15.after s a (pointer p) parents w [] issued consumed)).state =
      (stage (returned s a p) a parents (PV_THR2_F170.live.body.drop 17) w [] [] []).state := by
  have full := PV_LIB_A_ActiveDelivery17.consume cut (config s a parents p) (wait s p)
    PV_LIB_SPEC_Tls277Request15.site w [] issued consumed token s.nextActivation 6 [pointer p]
    ⟨.returned (.ok (value p)),w,[]⟩ (quiet s a parents p w) rfl rfl rfl rfl rfl rfl (by rfl)
    (fun resources => PV_LIB_SPEC_Tls277Bound15.answer cut resources (config s a parents p) w
      s.nextActivation p (wait s p) rfl rfl)
  have result := congrArg Execution.state full
  exact result

/-- Source request then named277 full delivery, on the original context machine. -/
theorem run (cut : PV_LIB_SPEC_ReachedNative14.Cut) (s : Store Data) (a : Nat)
    (parents : List Frame) (p : Address) (w : OWNER) (issued : List Issued) (consumed : List Context)
    (bound : s.cells ⟨a,7,[]⟩ = some (pointer p)) :
    (PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 4
      (stage s a parents (PV_THR2_F170.live.body.drop 14) w [] issued consumed)).state =
      (stage (returned s a p) a parents (PV_THR2_F170.live.body.drop 17) w [] [] []).state := by
  rw [show 4=3+1 from rfl,PV_LIB_SPEC_Original14.run_add,
    PV_LIB_SPEC_Tls277Request15.request cut _ s a (pointer p) parents w [] issued consumed bound]
  exact consume cut s a parents p w issued consumed

#print axioms quiet
#print axioms consume
#print axioms run
end PV_LIB_A_ActivePure27717
