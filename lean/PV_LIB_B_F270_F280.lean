import PV_LIB_A_PurePoll
import PV_LIB_A_WriterSites
import PV_THR2_F270
set_option autoImplicit false
noncomputable section
namespace PV_LIB_B_F270_F280
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame
/-- Decode only the actual emitted Regular/local-destination call shape. -/
def decode : PV_STX2_SliceSyntax.Node → PV_FN_W4_CallBoundary.Call
  | .leaf (.call site (.object [("Regular",.object [("kind",kind),("generics",g)])]) args (.local dest) []) =>
      ⟨site,kind,g,args,dest⟩
  | _ => ⟨⟨0,0,.null⟩,.null,.null,[],0⟩
def call0 := decode PV_THR2_F270.node49
theorem source0 : PV_FN_W4_CallBoundary.node call0 = PV_THR2_F270.node49 := rfl
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
abbrev closed_root := @PV_W1_NativeLeaves.f280

def model {E : Type} (C : Carrier OWNER Data) (H : Backend E)
    (d : Entry) (w : OWNER) (es : List E) :=
  PV_LIB.observe (deliver C d (PV_THR2_OwnUniformResourceHandler.lift H
    (.child d.callee d.store.nextActivation d.arguments) w) es)
def law {E : Type} (C : Carrier OWNER Data) (H : Backend E)
    (d : Entry) (w : OWNER) (es : List E) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model C H d w es
/-- The provider's own generic administration proof, instantiated with the
actual polymorphic token. No generic metadata is erased or identified. -/
theorem certified {E : Type} (C : Carrier OWNER Data) (H : Backend E)
    (d : Entry) (w : OWNER) (es : List E) :
    PV_W1_LeafBoundary.Post d (PV_THR2_OwnUniformResourceHandler.lift H
      (.child d.callee d.store.nextActivation d.arguments) w) es
      (deliver C d (PV_THR2_OwnUniformResourceHandler.lift H
        (.child d.callee d.store.nextActivation d.arguments) w) es) :=
  PV_W1_LeafBoundary.full_reply C d _ es

theorem actual_machine0 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Backend E)
    (values : PV_THR2_SourceStoreLibrary.Values OWNER E)
    (t : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (vs : List Data) (stack : List Config)
    (w : OWNER) (es : List E) (leaf : P (PV_FN_W4_CallBoundary.token call0) = none) :
    let d := entry call0 t a parents loops rest vs stack
    law C H d w es (PV_LIB.observe (PV_THR2_SourceStoreInterpreter.step C K P
      (PV_THR2_OwnUniformResourceHandler.lift H) values
      ⟨⟨.running (pending d),w,es⟩,stack⟩)) := by
  let d := entry call0 t a parents loops rest vs stack
  have other : d.callee ≠ PV_THR2_Catch219Call318.fn := by
    intro h
    have bad := congrArg PV_THR2_OffPath.functionId h
    change some 280 = some 318 at bad
    cases bad
  exact congrArg PV_LIB.observe (PV_LIB_A_PurePoll.unlisted_poll C K P H values d w es
    (PV_LIB_A_PurePoll.noncatch d other) leaf (by rfl))
#print axioms actual_machine0
#print axioms caller_domain
#print axioms closed_root
#print axioms model
#print axioms law
#print axioms certified
end PV_LIB_B_F270_F280
