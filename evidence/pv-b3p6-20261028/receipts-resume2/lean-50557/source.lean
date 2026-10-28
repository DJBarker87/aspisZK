import PV_B3P_NativeList226
namespace PV_B3P_NativePlan226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_RustResult PV_B3P_ByteLayout226V3 PV_B3P_NativeSteps226
set_option autoImplicit false

def indexSlice (v : U64) : Slice U8 :=
  ⟨(core.num.U64.to_le_bytes v).val, by
    rw [← PV_B3P_EndianVerified226V3.index_bytes]
    change 8 ≤ Usize.max
    scalar_tac⟩
theorem index_slice_value (v : U64) : (indexSlice v).val = indexBytes v :=
  (PV_B3P_EndianVerified226V3.index_bytes v).symm

def plan (p : reference226.OwnedPublic) : List Step := [
  .push (if p.withdrawal then 1#u8 else 0#u8),
  .fields p.anchor.val,
  .fields p.nullifier.val,
  .fields [p.asset_id],
  .push (if p.withdrawal then 0#u8 else 1#u8),
  .fields (if p.withdrawal then [] else p.recipient.val),
  .fields p.change.val,
  .push (if p.withdrawal then 1#u8 else 0#u8),
  .fields (if p.withdrawal then [p.withdrawal_amount] else []),
  .bytes (indexSlice p.next_pair_index),
  .fields (frontier p.frontier),
  .fields p.next_root.val,
  .fields (frontier p.next_frontier) ]

theorem payload_value (p : reference226.OwnedPublic) :
    PV_B3P_NativeList226.payload (plan p) = layout p := by
  cases hw : p.withdrawal <;>
    simp only [plan,PV_B3P_NativeList226.payload,PV_B3P_NativeList226.contents,
      layout,hw,Bool.false_eq_true,↓reduceIte,index_slice_value,
      fields,List.flatMap_nil,List.append_nil,List.nil_append,List.append_assoc]

theorem budget_bound (p : reference226.OwnedPublic) : budget (plan p) ≤ Usize.max := by
  rw [← PV_B3P_NativeList226.payload_length,payload_value,layout_length]
  have hm : 1455 ≤ Usize.max := by scalar_tac
  split <;> omega

def empty : alloc.vec.Vec U8 := ⟨[],by scalar_tac⟩
def native (p : reference226.OwnedPublic) := runVec empty (plan p)

theorem complete_result (p : reference226.OwnedPublic) :
    mapR (fun v : alloc.vec.Vec U8 => v.val) (native p) =
      if PV_B3P_NativeList226.valid (plan p) then .ok (.Ok (layout p))
      else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public) := by
  unfold native
  rw [PV_B3P_NativeSteps226.complete_result empty (plan p) (by exact budget_bound p),
      PV_B3P_NativeList226.complete_result,payload_value]
  rfl

#print axioms index_slice_value
#print axioms payload_value
#print axioms budget_bound
#print axioms complete_result
end PV_B3P_NativePlan226
