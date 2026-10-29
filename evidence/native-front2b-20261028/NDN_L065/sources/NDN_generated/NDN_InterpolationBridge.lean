import NDE_Reference14.Funs
import NDE_RawBridge
import NDE_RowBridge
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace NDN_InterpolationBridge

theorem return_bind {α : Type} (r : Result α) : (do let x ← r;ok x)=r := by
 cases r <;> rfl

theorem reduce (x : U64) :
 NDE_Reference14.reduce_ref x=FIq_Native.field.reduce_u64 x := by
 change NDE_Reference2.reduce_ref x=FIq_Native.field.reduce_u64 x
 exact NDE_RawBridge.reduce_kernel x

theorem source (w c : Array U32 3#usize) :
 NDE_Reference14.interpolation_limb_ref w c = (do
  let w0 ← Array.index_usize w 0#usize
  let w1 ← Array.index_usize w 1#usize
  let w2 ← Array.index_usize w 2#usize
  let c0 ← Array.index_usize c 0#usize
  let c1 ← Array.index_usize c 1#usize
  let c2 ← Array.index_usize c 2#usize
  FIq_Native.state_only_poseidon.interpolate_three_constant_limb w0 w1 w2 c0 c1 c2) := by
 obtain ⟨w0,hw0,_⟩:=NDE_RowBridge.read_total w 0#usize (by decide)
 obtain ⟨w1,hw1,_⟩:=NDE_RowBridge.read_total w 1#usize (by decide)
 obtain ⟨w2,hw2,_⟩:=NDE_RowBridge.read_total w 2#usize (by decide)
 obtain ⟨c0,hc0,_⟩:=NDE_RowBridge.read_total c 0#usize (by decide)
 obtain ⟨c1,hc1,_⟩:=NDE_RowBridge.read_total c 1#usize (by decide)
 obtain ⟨c2,hc2,_⟩:=NDE_RowBridge.read_total c 2#usize (by decide)
 simp only [NDE_Reference14.interpolation_limb_ref,
  FIq_Native.state_only_poseidon.interpolate_three_constant_limb,
  hw0,hw1,hw2,hc0,hc1,hc2,bind_tc_ok,bind_assoc_eq,reduce,lift,
  FIq_Native.field.M31.reduce_u64,return_bind]
 rfl

#print axioms return_bind
#print axioms reduce
#print axioms source
end NDN_InterpolationBridge
end
