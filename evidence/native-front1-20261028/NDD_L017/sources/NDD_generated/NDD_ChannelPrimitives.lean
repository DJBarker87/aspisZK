import NDD_Reference.Funs
import NDD_ResultLaws
import FIq_Native01
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_ChannelPrimitives
open FIq_Native

theorem add (x y : U32) : NDD_Reference.add_ref x y = field.M31.add x y := by
  simp [NDD_Reference.add_ref,field.M31.add,field.P]
theorem sub (x y : U32) : NDD_Reference.sub_ref x y = field.M31.sub x y := by
  simp [NDD_Reference.sub_ref,field.M31.sub,field.P]
theorem reduce (x : U64) : NDD_Reference.reduce_u62_ref x = field.M31.reduce_u64 x := by
  simp only [NDD_Reference.reduce_u62_ref,field.M31.reduce_u64,field.reduce_u64,field.P]
  simp
  rfl

def cArray (x : field.CM31) : Array U32 2#usize := Array.make 2#usize [x.a,x.b]
theorem reconstruct (x : Array U64 3#usize) :
    NDD_Reference.reconstruct_ref x = (do
      let c ← field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call () x
      ok (cArray c)) := by
  simp [NDD_Reference.reconstruct_ref,
    field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call,
    sub,reduce,cArray]

#print axioms add
#print axioms sub
#print axioms reduce
#print axioms reconstruct
end NDD_ChannelPrimitives
