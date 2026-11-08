import PV_LIB_A_ChainTrace11
import PV_THR2_ScopePrologue
import PV_THR2_ScopeReply121
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F6Prefix11
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_THR2_IntrinsicFrameChain

def prepend (node : PV_STX2_SliceSyntax.Node) (next : Chain) : Chain :=
  match node with
  | .leaf (.storage site live slot) => .storage site live slot next
  | .leaf (.bind site dest expr) => .bind site dest expr next
  | _ => .done

/-- Exact emitted scope prologue; shape below rules out any discarded node. -/
def prologue : Chain :=
  prepend PV_THR2_F6.node0 (
    prepend PV_THR2_F6.node1 (
    prepend PV_THR2_F6.node2 (
    prepend PV_THR2_F6.node3 (
    prepend PV_THR2_F6.node4 (
    prepend PV_THR2_F6.node5 (
    prepend PV_THR2_F6.node6 (
    prepend PV_THR2_F6.node7 (
    prepend PV_THR2_F6.node8 (
    prepend PV_THR2_F6.node9 (
    prepend PV_THR2_F6.node10 (
    prepend PV_THR2_F6.node11 (
    prepend PV_THR2_F6.node12 (
    prepend PV_THR2_F6.node13 (
    prepend PV_THR2_F6.node14 (
    prepend PV_THR2_F6.node15 (.done))))))))))))))))

theorem shape : nodes prologue ++ PV_THR2_F6.live.body.drop 16 = PV_THR2_F6.live.body := rfl

theorem sites : PV_LIB_A_ChainTrace11.Sites prologue := by
  simp [prologue,prepend,PV_LIB_A_ChainTrace11.Sites,PV_THR2_F6.node0,PV_THR2_F6.node1,PV_THR2_F6.node2,PV_THR2_F6.node3,PV_THR2_F6.node4,PV_THR2_F6.node5,PV_THR2_F6.node6,PV_THR2_F6.node7,PV_THR2_F6.node8,PV_THR2_F6.node9,PV_THR2_F6.node10,PV_THR2_F6.node11,PV_THR2_F6.node12,PV_THR2_F6.node13,PV_THR2_F6.node14,PV_THR2_F6.node15]

/-- One symbolic binding lemma, reused before reducing any chain fuel. -/
theorem literal_bound (C : Carrier OWNER Data) (s : Store Data) (a dst : Nat)
    (w : OWNER) (literal value : Data) (constant : C.constant literal = some value) :
    bound C s a (.local dst) (.use (.constant literal)) w =
      some (write s ⟨a,dst,[]⟩ (some value)) := by
  simp [bound,PV_STX2_Store.bind,evaluate,operand,writeAddress,locate,constant]

/-- Sixteen administrative source instructions, no unbounded reduction. -/
theorem steps16 (C : Carrier OWNER Data) (s : Store Data) (a : Nat) (b : Bool) (w : OWNER) :
    steps (PV_THR2_EntryDynamic.carrier C b) a w prologue s = 16 := by
  have hf (t : Store Data) (dst : Nat) := literal_bound
    (PV_THR2_EntryDynamic.carrier C b) t a dst w PV_THR2_ScopePrologue.literals.1 (.boolean false) (by rfl)
  have ht (t : Store Data) (dst : Nat) := literal_bound
    (PV_THR2_EntryDynamic.carrier C b) t a dst w PV_THR2_ScopePrologue.literals.2 (.boolean true) (by rfl)
  simp only [PV_THR2_ScopePrologue.literals,PV_THR2_F6.node6,PV_THR2_F6.node11] at hf ht
  simp [prologue,prepend,PV_THR2_F6.node0,PV_THR2_F6.node1,PV_THR2_F6.node2,PV_THR2_F6.node3,PV_THR2_F6.node4,PV_THR2_F6.node5,PV_THR2_F6.node6,PV_THR2_F6.node7,PV_THR2_F6.node8,PV_THR2_F6.node9,PV_THR2_F6.node10,PV_THR2_F6.node11,PV_THR2_F6.node12,PV_THR2_F6.node13,PV_THR2_F6.node14,PV_THR2_F6.node15,steps,hf,ht]

theorem result16 (C : Carrier OWNER Data) (s : Store Data) (a : Nat) (parents : List Frame)
    (b : Bool) (w : OWNER) :
    result (PV_THR2_EntryDynamic.carrier C b) a parents [] (PV_THR2_F6.live.body.drop 16)
      w prologue s = .running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 16},
        parents,PV_THR2_ScopePrologue.prepared s a⟩ := rfl

/-- Corrected-machine history from the actual f6 body entry, with every source
store symbolic. No predecessor f0/OwnInit entry-to-f6 history is asserted. -/
theorem prologue_run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_LIB_StoreActionTable.Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    PV_LIB_A_PrefixMachine11.advance (PV_THR2_EntryDynamic.carrier C b) K P resources encode H values 16
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body},parents,s⟩,w,es⟩,stack⟩,none⟩ =
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 16},parents,
        PV_THR2_ScopePrologue.prepared s a⟩,w,es⟩,stack⟩,none⟩ := by
  have h := PV_LIB_A_ChainTrace11.corrected_run (PV_THR2_EntryDynamic.carrier C b) K P
    resources encode H values prologue s a parents [] (PV_THR2_F6.live.body.drop 16) w es stack sites
  rw [shape,steps16,result16] at h
  exact h

#print axioms shape
#print axioms sites
#print axioms literal_bound
#print axioms steps16
#print axioms result16
#print axioms prologue_run
end PV_LIB_A_F6Prefix11
