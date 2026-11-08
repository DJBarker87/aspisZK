import PV_LIB_A_SourceSequence13
import PV_LIB_A_Continuation12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_SequenceFrontier13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11 PV_LIB_A_SourceSequence13

/-- The exact-shape equality at each use checks that this parser discarded no
source instruction. Unsupported nodes do not acquire an interpretation. -/
def prepend (node : PV_STX2_SliceSyntax.Node) (tail : Seq) : Seq := match node with
  | .leaf (.storage site live slot) => .storage site live slot tail
  | .leaf (.bind site dest expr) => .bind site dest expr tail
  | .leaf (.aggregateMove site dest kind args) => .aggregate site dest kind args tail
  | _ => .done

def cost (C : Carrier OWNER Data) (seq : Seq) (c : Config) (w : OWNER) :=
  PV_LIB_A_SourceSequence13.steps C c.frame.activation w seq c.store

def finish (C : Carrier OWNER Data) (seq : Seq) (rest : List PV_STX2_SliceSyntax.Node)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) : State :=
  ⟨⟨result C c.frame.activation c.callers c.frame.loops rest w seq c.store,w,es⟩,stack⟩

def steps (C : Carrier OWNER Data) (seq : Seq) (rest : List PV_STX2_SliceSyntax.Node) (q : State) :=
  PV_THR2_IntrinsicAtContinuation.steps (nodes seq ++ rest) (cost C seq) q

def after (C : Carrier OWNER Data) (seq : Seq) (rest : List PV_STX2_SliceSyntax.Node) (q : State) :=
  PV_THR2_IntrinsicAtContinuation.after (nodes seq ++ rest) (finish C seq rest) q

/-- Arbitrary terminal/pending/unrelated frontiers consume zero fuel. A matching
source frontier executes precisely the certified sequence, preserving its loops,
parents, suspended frames, world and events and every failed-binding frontier. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (seq : Seq) (rest : List PV_STX2_SliceSyntax.Node) (off : sites seq) (q : State) :
    advance C K P resources encode H values (steps C seq rest q) ⟨q,none⟩ =
      ⟨after C seq rest q,none⟩ := by
  apply PV_LIB_A_Continuation12.run
  · intro c w es stack h
    rw [PV_THR2_IntrinsicAtContinuation.frame c h]
    exact (certified C K P H seq c.store c.frame.activation c.callers c.frame.loops rest w es stack off).1
  · intro c w es stack h
    rw [PV_THR2_IntrinsicAtContinuation.frame c h]
    exact (certified C K P H seq c.store c.frame.activation c.callers c.frame.loops rest w es stack off).2

#print axioms prepend
#print axioms cost
#print axioms finish
#print axioms steps
#print axioms after
#print axioms run
end PV_LIB_A_SequenceFrontier13
