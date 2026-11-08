"""One exact emitted call per slot, retaining generic metadata and all replies."""
from pathlib import Path
slots=[(537,612,[4],None),(361,279,[175],None),(361,280,[182],None),(270,279,[42],None),(270,280,[49],None),(15,167,[38,68,122],'vecPush167'),(15,9,[84],'intoIterNext9'),(15,93,[17],'rangeNext93'),(1,10,[125],'vecAppend10'),(1,9,[88],'intoIterNext9')]
for parent,child,nodes,meaning in slots:
 m=f'PV_LIB_B_F{parent}_F{child}'+('Fixed' if meaning else '')
 s=f'''import PV_LIB_A_PurePoll
import PV_LIB_A_WriterSites
import PV_THR2_F{parent}
set_option autoImplicit false
noncomputable section
namespace {m}
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame
/-- Decode only the actual emitted Regular/local-destination call shape. -/
def decode : PV_STX2_SliceSyntax.Node → PV_FN_W4_CallBoundary.Call
  | .leaf (.call site (.object [("Regular",.object [("kind",kind),("generics",g)])]) args (.local dest) []) =>
      ⟨site,kind,g,args,dest⟩
  | _ => ⟨⟨0,0,.null⟩,.null,.null,[],0⟩
'''
 for i,node in enumerate(nodes):
  s+=f'''def call{i} := decode PV_THR2_F{parent}.node{node}
theorem source{i} : PV_FN_W4_CallBoundary.node call{i} = PV_THR2_F{parent}.node{node} := rfl
#print axioms source{i}
'''
 s+='''
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
'''
 s+=f'''/-- Retain the exact CLOSED certificate separately from the corrected source
projection. Its arbitrary argument effects do not assert source-value adequacy. -/
abbrev closed_root := @PV_W1_NativeLeaves.f{child}
'''
 if meaning is None:
  s+='''
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
'''
  for i in range(len(nodes)):
   s+=f'''
theorem actual_machine{i} {{E : Type}} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Backend E)
    (values : PV_THR2_SourceStoreLibrary.Values OWNER E)
    (t : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (vs : List Data) (stack : List Config)
    (w : OWNER) (es : List E) (leaf : P (PV_FN_W4_CallBoundary.token call{i}) = none) :
    let d := entry call{i} t a parents loops rest vs stack
    law C H d w es (PV_LIB.observe (PV_THR2_SourceStoreInterpreter.step C K P
      (PV_THR2_OwnUniformResourceHandler.lift H) values
      ⟨⟨.running (pending d),w,es⟩,stack⟩)) := by
  let d := entry call{i} t a parents loops rest vs stack
  have other : d.callee ≠ PV_THR2_Catch219Call318.fn := by
    intro h
    have bad := congrArg PV_THR2_OffPath.functionId h
    change some {child} = some 318 at bad
    cases bad
  exact congrArg PV_LIB.observe (PV_LIB_A_PurePoll.unlisted_poll C K P H values d w es
    (PV_LIB_A_PurePoll.noncatch d other) leaf (by rfl))
#print axioms actual_machine{i}
'''
 else:
  s+=f'''
def model (C : Carrier OWNER Data)
    (values : PV_THR2_SourceStoreLibrary.Values OWNER PV_RJ4IDB.NativeEvent)
    (d : Entry) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent)
    (reply : Reply OWNER PV_RJ4IDB.NativeEvent Data) :=
  PV_LIB_A_SourceWriters.model C values (pending d) w es d.suspended
    (PV_LIB_A_WriterSites.site d .{meaning}) reply
def law (C : Carrier OWNER Data)
    (values : PV_THR2_SourceStoreLibrary.Values OWNER PV_RJ4IDB.NativeEvent)
    (d : Entry) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent)
    (reply : Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model C values d w es reply
'''
  for i in range(len(nodes)):
   s+=f'''
/-- Corrected OWNER-aware machine, exact issued operands and named write
meaning. Malformed/undefined and every non-success reply remain in the graph. -/
theorem actual_machine{i} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (resources : PV_EVHB_OwnerHeap.Resources) (encode : PV_EVHB_OwnerHeap.Encode)
    (H : PV_LIB_A_OwnerStore.Handler)
    (values : PV_THR2_SourceStoreLibrary.Values OWNER PV_RJ4IDB.NativeEvent)
    (t : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (vs : List Data) (stack : List Config)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent)
    (leaf : P (PV_FN_W4_CallBoundary.token call{i}) = none) :
    let d := entry call{i} t a parents loops rest vs stack
    law C values d w es
      (H (PV_LIB_A_WriterSites.site d .{meaning}).waiting.request w)
      (PV_LIB.observe (PV_LIB_A_OwnerStore.step C K P resources encode H values
        ⟨⟨.running (pending d),w,es⟩,stack⟩)) := by
  let d := entry call{i} t a parents loops rest vs stack
  have other : d.callee ≠ PV_THR2_Catch219Call318.fn := by
    intro h
    have bad := congrArg PV_THR2_OffPath.functionId h
    change some {child} = some 318 at bad
    cases bad
  exact PV_LIB_A_WriterSites.installed C K P resources encode H values d .{meaning} w es leaf
    (by rfl) (PV_LIB_A_PurePoll.noncatch d other)
#print axioms actual_machine{i}
'''
 s+='''#print axioms caller_domain
#print axioms closed_root
#print axioms model
#print axioms law
'''
 if meaning is None:s+='#print axioms certified\n'
 s+=f'end {m}\n'
 Path('lean',m+'.lean').write_text(s)
