import PV_LIB_SPEC_SparseArc
import PV_LIB_SPEC_FrozenABI
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_SparsePacketHandler
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
local instance : DecidableEq Data := Classical.decEq _

/-- Resolve a physical allocation address FROM its actual registered source
backing. This partial codec does not invent bytes for unregistered pointers. -/
def physical (C : Carrier OWNER Data) (w : OWNER) (pointer : Data) : Option Nat := do
  let address ← C.dereference w pointer
  let (_,header) ← receiver w ⟨address.activation,address.localIndex :: address.fields⟩
  pure header.pointer

/-- N95807 Arc<ScopeData> is Option(Arc(NonNull(pointer))). None is null;
Some follows the source wrappers to the registered allocation's physical base.
This is a source-to-native codec target, not a pointer alias assumption. -/
def scopeWord (C : Carrier OWNER Data) (K : PV_STX2_SliceMachine.Control)
    (w : OWNER) (scope : Data) : Option Nat := do
  match K.variant scope with
  | some 0 => some 0
  | some 1 =>
    let arc ← C.field scope 0
    let nonNull ← C.field arc 0
    let pointer ← C.field nonNull 0
    physical C w pointer
  | _ => none

/-- Decode ONLY the initial Packet shape of the adopted four stores. The
source AtomicUsize wrappers must contain1, result UnsafeCell must contain None.
Malformed source Data has no byte image. No future-success premise is used. -/
def decode (C : Carrier OWNER Data) (K : PV_STX2_SliceMachine.Control)
    (w : OWNER) (strong weak packet : Data) : Option Nat := do
  let sCell ← C.field strong 0
  let .number 1 ← C.field sCell 0 | none
  let wCell ← C.field weak 0
  let .number 1 ← C.field wCell 0 | none
  let scope ← C.field packet 0
  let resultCell ← C.field packet 1
  let result ← C.field resultCell 0
  if K.variant result = some 0 then scopeWord C K w scope else none

/-- Exact 4963 token/kind/activation selection. The allocation is issued for
all answers. Only nonnull success invokes the partial sparse codec; failed
source decoding remains explicit None, never arbitrary total-image fallback. -/
def handler (C : Carrier OWNER Data) (K : PV_STX2_SliceMachine.Control)
    (resources : Resources) (encode : Encode) (s : Store Data)
    (fallback : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (request : PV_STX2_Native.Request Data) (w : OWNER) :
    Option (Reply OWNER PV_RJ4IDB.NativeEvent Data) :=
  match request with
  | .child fn a [.object [("thread-aggregate-kind",kind),
      ("thread-aggregate-slots",.array [.array [strong],.array [weak],.array [packet]])]] =>
    if fn = PV_THR2_Packet124BoxIssue17.fn ∧ a = s.nextActivation ∧
        kind = PV_THR2_Packet124Aggregate13.source.2.2.1 then
      let r := PV_THR2_PacketBoxResource.reply resources encode s w PV_LIB_SPEC_SparseArc.shape 8
      match r.answer with
      | .returned (.ok p) => if p=0 then some (PV_LIB_SPEC_SparseArc.reply resources encode s w 0)
        else do
          let scope ← decode C K w strong weak packet
          some (PV_LIB_SPEC_SparseArc.reply resources encode s w scope)
      | _ => some (PV_LIB_SPEC_SparseArc.reply resources encode s w 0)
    else some (fallback request w)
  | _ => some (fallback request w)

/-- Full off-token reply identity; no return-success or write-definedness
antecedent is introduced into a machine specification. -/
theorem away (C : Carrier OWNER Data) (K : PV_STX2_SliceMachine.Control)
    (resources : Resources) (encode : Encode) (s : Store Data)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (fn : Data) (a : Nat) (kind strong weak packet : Data) (w : OWNER)
    (other : fn ≠ PV_THR2_Packet124BoxIssue17.fn) :
    handler C K resources encode s H
      (.child fn a [PV_THR2_KeyValues.pack kind [strong,weak,packet]]) w =
      some (H (.child fn a [PV_THR2_KeyValues.pack kind [strong,weak,packet]]) w) := by
  simp only [handler,PV_THR2_KeyValues.pack,List.map_cons,List.map_nil,other,false_and,if_false]

/-- Local source association, to be derived at the actual reached operand.
This is a conditional codec lemma, NOT an endpoint/row hypothesis. -/
theorem at_call (C : Carrier OWNER Data) (K : PV_STX2_SliceMachine.Control)
    (resources : Resources) (encode : Encode) (s : Store Data)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (w : OWNER) (strong weak packet : Data) (scope p : Nat)
    (allocation : (resources (.malloc 48) (world w)).answer = .returned (.ok p))
    (nonnull : p ≠ 0) (decoded : decode C K w strong weak packet = some scope) :
    handler C K resources encode s H
      (.child PV_THR2_Packet124BoxIssue17.fn s.nextActivation
        [PV_THR2_KeyValues.pack PV_THR2_Packet124Aggregate13.source.2.2.1 [strong,weak,packet]]) w =
      some (PV_LIB_SPEC_SparseArc.reply resources encode s w scope) := by
  have resource := (PV_THR2_PacketBoxResource.answer resources encode s w PV_LIB_SPEC_SparseArc.shape 8).trans allocation
  simp only [handler,PV_THR2_KeyValues.pack,List.map_cons,List.map_nil,and_self,ite_true,
    resource,if_neg nonnull,decoded]
  rfl

#print axioms physical
#print axioms scopeWord
#print axioms decode
#print axioms handler
#print axioms away
#print axioms at_call
end PV_LIB_SPEC_SparsePacketHandler
