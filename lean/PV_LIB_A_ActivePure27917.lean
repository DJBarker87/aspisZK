import PV_LIB_A_ActivePure27817
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace PV_LIB_A_ActivePure27917
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)
open PV_LIB_SPEC_Tls279Values16 (token value)

def config (s : Store Data) (a : Nat) (parents : List Frame) (p : Address) : Config :=
  PV_LIB_SPEC_Tls279Request16.config s a parents (PV_LIB_SPEC_Tls278Values15.value p)
def wait (s : Store Data) (p : Address) : PV_STX2_Native.Waiting Data :=
  ⟨.child token s.nextActivation [PV_LIB_SPEC_Tls278Values15.value p],
    .child s.nextActivation (.local 4),[]⟩
def pending (s : Store Data) (a : Nat) (parents : List Frame) (p : Address) (w : OWNER)
    (issued : List Issued) (consumed : List Context) : Execution :=
  ⟨⟨⟨.running (config s a parents p),w,[]⟩,[]⟩,
    ⟨PV_LIB_SPEC_Tls279History16.site,a,(wait s p).request⟩::issued,consumed⟩
def returned (s : Store Data) (a : Nat) (p : Address) : Store Data :=
  write (write (config s a [] p).store ⟨s.nextActivation,0,[]⟩ (some (value p))) ⟨a,4,[]⟩ (some (value p))

theorem source (cut : PV_LIB_SPEC_ReachedNative14.Cut) (s : Store Data) (a : Nat)
    (parents : List Frame) (p : Address) (w : OWNER) (issued : List Issued) (consumed : List Context)
    (bound : s.cells ⟨a,5,[]⟩ = some (PV_LIB_SPEC_Tls278Values15.value p)) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 3
      (stage s a parents (PV_THR2_F170.live.body.drop 21) w [] issued consumed) =
      pending s a parents p w issued consumed := by
  let H : Handler := fun _ w => ⟨.pending,w,[]⟩
  rw [PV_LIB_SPEC_SourceTransport15.run cut _ H _ _
    (PV_LIB_SPEC_Tls279Request16.trace cut _ H s a parents w [] issued consumed)]
  apply PV_LIB_A_F170Return16.execution_ext
  · rw [PV_LIB_SPEC_SourceProjection15.state]
    exact PV_LIB_SPEC_Tls279Request16.source _ H s a parents (PV_LIB_SPEC_Tls278Values15.value p) w [] bound
  · exact PV_LIB_SPEC_Tls279History16.issued _ H s a parents _ w [] issued consumed bound
  · exact PV_LIB_SPEC_Tls279History16.consumed _ H _ _

theorem quiet (s : Store Data) (a : Nat) (parents : List Frame) (p : Address) (w : OWNER) :
    PV_LIB_SPEC_SourceTransport15.Quiet ⟨⟨.running (config s a parents p),w,[]⟩,[]⟩ := by
  have lookup : PV_LIB_SPEC_Full.programs PV_THR2_RunTlsBranchRequest.callee = none := rfl
  have table : PV_LIB_StoreActionTable.v2 PV_THR2_RunTlsBranchRequest.callee = none := rfl
  have head : PV_THR2_F170.live.body.drop 24 = PV_THR2_F170.node24 :: PV_THR2_F170.live.body.drop 25 := rfl
  simp [PV_LIB_SPEC_SourceTransport15.Quiet,PV_LIB_StoreActionTable.Neutral,PV_LIB_StoreActionTable.select,
    config,PV_LIB_SPEC_Tls279Request16.config,PV_THR2_RunTlsBranchRequest.pending,
    PV_THR2_OwnInitAction.selected,PV_THR2_OperatorAction.selected,PV_THR2_OperatorAction.instruction,
    PV_THR2_OwnUniformNeutral.configuration,PV_THR2_OwnUniformNeutral.instruction,
    head,PV_THR2_F170.node24,lookup,table]

theorem consume (cut : PV_LIB_SPEC_ReachedNative14.Cut) (s : Store Data) (a : Nat)
    (parents : List Frame) (p : Address) (w : OWNER) (issued : List Issued) (consumed : List Context) :
    (PV_LIB_SPEC_ReachedNative14.step cut PV_LIB_SPEC_ReachedEnvironment14.parameters
      (pending s a parents p w issued consumed)).state =
      (stage (returned s a p) a parents (PV_THR2_F170.live.body.drop 24) w [] [] []).state := by
  have full := PV_LIB_A_ActiveDelivery17.consume cut (config s a parents p) (wait s p)
    PV_LIB_SPEC_Tls279History16.site w [] issued consumed token s.nextActivation 4
    [PV_LIB_SPEC_Tls278Values15.value p]
    ⟨.returned (.ok (value p)),w,[]⟩ (quiet s a parents p w) rfl rfl rfl rfl rfl rfl (by rfl)
    (fun resources => PV_LIB_SPEC_Tls279Bound16.answer cut resources (config s a parents p) w
      s.nextActivation p (wait s p) rfl rfl)
  have result := congrArg Execution.state full
  exact result

theorem run (cut : PV_LIB_SPEC_ReachedNative14.Cut) (s : Store Data) (a : Nat)
    (parents : List Frame) (p : Address) (w : OWNER) (issued : List Issued) (consumed : List Context)
    (bound : s.cells ⟨a,5,[]⟩ = some (PV_LIB_SPEC_Tls278Values15.value p)) :
    (PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 4
      (stage s a parents (PV_THR2_F170.live.body.drop 21) w [] issued consumed)).state =
      (stage (returned s a p) a parents (PV_THR2_F170.live.body.drop 24) w [] [] []).state := by
  rw [show 4=3+1 from rfl,PV_LIB_SPEC_Original14.run_add,source cut s a parents p w issued consumed bound]
  exact consume cut s a parents p w issued consumed

#print axioms source
#print axioms quiet
#print axioms consume
#print axioms run
end PV_LIB_A_ActivePure27917
