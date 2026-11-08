import PV_LIB_A_PurePoll
import PV_LIB_A_WriterSites
import PV_THR2_F15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_B_F15_F9Fixed
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame
/-- Decode only the actual emitted Regular/local-destination call shape. -/
def decode : PV_STX2_SliceSyntax.Node → PV_FN_W4_CallBoundary.Call
  | .leaf (.call site (.object [("Regular",.object [("kind",kind),("generics",g)])]) args (.local dest) []) =>
      ⟨site,kind,g,args,dest⟩
  | _ => ⟨⟨0,0,.null⟩,.null,.null,[],0⟩
def call0 := decode PV_THR2_F15.node84
theorem source0 : PV_FN_W4_CallBoundary.node call0 = PV_THR2_F15.node84 := rfl
#print axioms source0

def entry (call : PV_FN_W4_CallBoundary.Call) (t : Store Data) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (rest : List PV_STX2_SliceSyntax.Node)
    (vs : List Data) (stack : List Config) :=
  PV_FN_W4_NativeContract.entry t a parents loops rest call vs stack
/-- Domain at the SAME issued store; operand moves preserve its counter. -/
theorem caller_domain (call : PV_FN_W4_CallBoundary.Call)
    (C : Carrier OWNER Data) (s t : Store Data) (w : OWNER) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (rest : List PV_STX2_SliceSyntax.Node)
    (vs : List Data) (stack : List Config)
    (wf : PV_W1_OwnerWellFormed.OwnerWellFormed w s.nextActivation)
    (evaluated : PV_FN_W4_NativeContract.evaluated C s w a call = some (vs,t)) :
    PV_W1_NativeLeaves.Pre (entry call t a parents loops rest vs stack) w := by
  change PV_W1_OwnerWellFormed.OwnerWellFormed w t.nextActivation
  rw [PV_FN_W4_NativeContract.counter C s t w a call vs evaluated]
  exact wf
/-- Retain the exact CLOSED certificate separately from the corrected source
projection. Its arbitrary argument effects do not assert source-value adequacy. -/
abbrev closed_root := @PV_W1_NativeLeaves.f9

def model (C : Carrier OWNER Data)
    (values : PV_THR2_SourceStoreLibrary.Values OWNER PV_RJ4IDB.NativeEvent)
    (d : Entry) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent)
    (reply : Reply OWNER PV_RJ4IDB.NativeEvent Data) :=
  PV_LIB_A_SourceWriters.model C values (pending d) w es d.suspended
    (PV_LIB_A_WriterSites.site d .intoIterNext9) reply
def law (C : Carrier OWNER Data)
    (values : PV_THR2_SourceStoreLibrary.Values OWNER PV_RJ4IDB.NativeEvent)
    (d : Entry) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent)
    (reply : Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model C values d w es reply

/-- Corrected OWNER-aware machine, exact issued operands and named write
meaning. Malformed/undefined and every non-success reply remain in the graph. -/
theorem actual_machine0 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (resources : PV_EVHB_OwnerHeap.Resources) (encode : PV_EVHB_OwnerHeap.Encode)
    (H : PV_LIB_A_OwnerStore.Handler)
    (values : PV_THR2_SourceStoreLibrary.Values OWNER PV_RJ4IDB.NativeEvent)
    (t : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (vs : List Data) (stack : List Config)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent)
    (leaf : P (PV_FN_W4_CallBoundary.token call0) = none) :
    let d := entry call0 t a parents loops rest vs stack
    law C values d w es
      (H (PV_LIB_A_WriterSites.site d .intoIterNext9).waiting.request w)
      (PV_LIB.observe (PV_LIB_A_OwnerStore.step C K P resources encode H values
        ⟨⟨.running (pending d),w,es⟩,stack⟩)) := by
  let d := entry call0 t a parents loops rest vs stack
  have other : d.callee ≠ PV_THR2_Catch219Call318.fn := by
    intro h
    have bad := congrArg PV_THR2_OffPath.functionId h
    change some 9 = some 318 at bad
    cases bad
  exact PV_LIB_A_WriterSites.installed C K P resources encode H values d .intoIterNext9 w es leaf
    (by rfl) (PV_LIB_A_PurePoll.noncatch d other)
#print axioms actual_machine0
#print axioms caller_domain
#print axioms closed_root
#print axioms model
#print axioms law
end PV_LIB_B_F15_F9Fixed
