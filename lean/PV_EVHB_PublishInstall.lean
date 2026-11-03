import PV_EVHB_PublishCompact
import PV_EVH_CapacityWorld
import PV_EVH_RuntimeOperators
set_option autoImplicit false
noncomputable section
namespace PV_EVHB_PublishInstall
open Aeneas Aeneas.Std ProverRwFull PV_EVH_Runtime
open PV_EVH_AllocatorWorld
open PV_RJ4IDB (Bytes NativeEvent)
variable [ExternalTypes] [ExternalFuns]
/- Partial source transport, including runtime-fault worlds. LayoutFamily,
allocator/native heap ownership and initialized-region/drop/encoding fidelity
are separate P obligations; this does not discharge them. -/
structure Leaves where
  op242_OPEN : Q (Std.Usize)
  op245_OPEN : Q ((Array Std.U8 8#usize))
  extendFromSlice_OPEN : ∀ {T : Type} (inst : core.clone.Clone T) (v : alloc.vec.Vec T) (s : Slice T), Q (alloc.vec.Vec T)
  op234_OPEN : ∀ (arg0 : transport.Variant), Q (Std.U8)
  compact_semantic_OPEN : ∀ (logical : Slice Std.U8) (out : alloc.vec.Vec Std.U8), Q (((core.result.Result Unit compact.CodecError) × (alloc.vec.Vec
    Std.U8)))
  compact_values_OPEN : ∀ (logical : Slice Std.U8) (out : alloc.vec.Vec Std.U8), Q (((core.result.Result Unit compact.CodecError) × (alloc.vec.Vec
    Std.U8)))
  op51_OPEN : ∀ (arg0 : aspis_core.field.wide_exact.WideExact), Q ((Array Std.U8 32#usize))
  op244_OPEN : Q (Std.Usize)
  assert_OPEN : ∀ (condition : Prop) [Decidable condition], Q (Unit)
  unwrap_OPEN : ∀ {T : Type} (value : Option T), Q (T)
  append_query_openings_OPEN : ∀ (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment)
  (cc2 : host_commitment.Commitment) (queries : Array Std.U32 22#usize)
  (folded_word : Slice aspis_core.field.wide_exact.WideExact)
  (folded_salts : host_commitment.PrivateSalts), Q ((alloc.vec.Vec Std.U8))
  op243_OPEN : Q (Std.Usize)
  append_node_slots_OPEN : ∀ (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment)
  (cc2 : host_commitment.Commitment) (tree : host_tree.BinaryTree)
  (queries : Array Std.U32 22#usize), Q ((core.result.Result (alloc.vec.Vec Std.U8) verifier.Error))

structure Compatible (c : Leaves) : Prop where
  op242_fixed : PartialView (c.op242_OPEN) (compact.PROOF_BYTES)
  op245_fixed : PartialView (c.op245_OPEN) (compact.MAGIC)
  extendFromSlice_fixed : ∀ {T : Type} (inst : core.clone.Clone T) (v : alloc.vec.Vec T) (s : Slice T), PartialView (c.extendFromSlice_OPEN inst v s) (alloc.vec.Vec.extend_from_slice inst v s)
  op234_fixed : ∀ (arg0 : transport.Variant), PartialView (c.op234_OPEN arg0) (transport.Variant.tag arg0)
  compact_semantic_fixed : ∀ (logical : Slice Std.U8) (out : alloc.vec.Vec Std.U8), PartialView (c.compact_semantic_OPEN logical out) (host_compact.compact_semantic logical out)
  compact_values_fixed : ∀ (logical : Slice Std.U8) (out : alloc.vec.Vec Std.U8), PartialView (c.compact_values_OPEN logical out) (host_compact.compact_values logical out)
  op51_fixed : ∀ (arg0 : aspis_core.field.wide_exact.WideExact), PartialView (c.op51_OPEN arg0) (aspis_core.field.wide_exact.WideExact.to_le_bytes arg0)
  op244_fixed : PartialView (c.op244_OPEN) (compact.OFF_OPENINGS)
  assert_fixed : ∀ (condition : Prop) [Decidable condition], PartialView (c.assert_OPEN condition) (massert condition)
  unwrap_fixed : ∀ {T : Type} (value : Option T), PartialView (c.unwrap_OPEN value) (core.option.Option.unwrap value)
  append_query_openings_fixed : ∀ (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment)
  (cc2 : host_commitment.Commitment) (queries : Array Std.U32 22#usize)
  (folded_word : Slice aspis_core.field.wide_exact.WideExact)
  (folded_salts : host_commitment.PrivateSalts), PartialView (c.append_query_openings_OPEN out cc1 cc2 queries folded_word folded_salts) (prover.append_query_openings out cc1 cc2 queries folded_word folded_salts)
  op243_fixed : PartialView (c.op243_OPEN) (compact.OFF_NODES)
  append_node_slots_fixed : ∀ (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment)
  (cc2 : host_commitment.Commitment) (tree : host_tree.BinaryTree)
  (queries : Array Std.U32 22#usize), PartialView (c.append_node_slots_OPEN out cc1 cc2 tree queries) (prover.append_node_slots out cc1 cc2 tree queries)

def install (c : Leaves) (frames : PV_EVH_RuntimeOperators.Frames)
    (allocator : Allocator) (encode : AllocationEvent → Bytes)
    (element : Type → Layout) (maxBytes owner : Nat)
    (overflowDiagnostics oomDiagnostics : List NativeEvent) : PV_EVHB_PublishCompact.Callees where
  op242_OPEN := c.op242_OPEN
  op245_OPEN := c.op245_OPEN
  extendFromSlice_OPEN := c.extendFromSlice_OPEN
  op234_OPEN := c.op234_OPEN
  compact_semantic_OPEN := c.compact_semantic_OPEN
  drop_OPEN := frames.drop
  compact_values_OPEN := c.compact_values_OPEN
  op51_OPEN := c.op51_OPEN
  op244_OPEN := c.op244_OPEN
  assert_OPEN := c.assert_OPEN
  unwrap_OPEN := c.unwrap_OPEN
  append_query_openings_OPEN := c.append_query_openings_OPEN
  op243_OPEN := c.op243_OPEN
  append_node_slots_OPEN := c.append_node_slots_OPEN
  withCapacity_OPEN := fun T n => PV_EVH_CapacityWorld.withCapacity allocator encode (element T).size (element T).align maxBytes owner overflowDiagnostics oomDiagnostics T n

theorem install_view (c : Leaves) (frames : PV_EVH_RuntimeOperators.Frames)
    (allocator : Allocator) (encode : AllocationEvent → Bytes)
    (element : Type → Layout) (maxBytes owner : Nat)
    (overflowDiagnostics oomDiagnostics : List NativeEvent)
    (hc : Compatible c) (hf : PV_EVH_RuntimeOperators.Compatible frames)
    (selected : PV_EVH_OperatorFrames.Selection (inferInstance : ExternalFuns)) :
    PV_EVHB_PublishCompact.Compatible
      (install c frames allocator encode element maxBytes owner overflowDiagnostics oomDiagnostics) where
  op242_fixed := hc.op242_fixed
  op245_fixed := hc.op245_fixed
  extendFromSlice_fixed := hc.extendFromSlice_fixed
  op234_fixed := hc.op234_fixed
  compact_semantic_fixed := hc.compact_semantic_fixed
  drop_fixed := fun value => hf.drop_view value
  compact_values_fixed := hc.compact_values_fixed
  op51_fixed := hc.op51_fixed
  op244_fixed := hc.op244_fixed
  assert_fixed := hc.assert_fixed
  unwrap_fixed := hc.unwrap_fixed
  append_query_openings_fixed := hc.append_query_openings_fixed
  op243_fixed := hc.op243_fixed
  append_node_slots_fixed := hc.append_node_slots_fixed
  withCapacity_fixed := fun T n => PV_EVH_CapacityWorld.capacity_view allocator encode (element T).size (element T).align maxBytes owner overflowDiagnostics oomDiagnostics T n

#print axioms install_view
end PV_EVHB_PublishInstall
