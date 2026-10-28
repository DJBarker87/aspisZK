import NDD_ChannelPrimitives
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_Channels
open FIq_Native NDD_ChannelPrimitives

def qArray (x : field.QM31) : Array U32 4#usize :=
  Array.make 4#usize [x.c0.a,x.c0.b,x.c1.a,x.c1.b]

theorem cadd (x y : field.CM31) :
    NDD_Reference.cadd_ref (cArray x) (cArray y) =
      (do let c ← field.CM31.add x y; ok (cArray c)) := by
  simp [NDD_Reference.cadd_ref,cArray,Array.index_usize,Array.make,
    NDD_ChannelPrimitives.add,field.CM31.add]
theorem csub (x y : field.CM31) :
    NDD_Reference.csub_ref (cArray x) (cArray y) =
      (do let c ← field.CM31.sub x y; ok (cArray c)) := by
  simp [NDD_Reference.csub_ref,cArray,Array.index_usize,Array.make,
    NDD_ChannelPrimitives.sub,field.CM31.sub]
theorem byr (x : field.CM31) :
    NDD_Reference.byr_ref (cArray x) =
      (do let c ← field.mul_by_r x; ok (cArray c)) := by
  simp [NDD_Reference.byr_ref,cArray,Array.index_usize,Array.make,
    NDD_ChannelPrimitives.add,NDD_ChannelPrimitives.sub,field.mul_by_r,
    field.M31.double]

theorem channels (sums : Array (Array U64 3#usize) 3#usize) :
    NDD_Reference.channels_ref sums =
      (do let q ← field.qm31_from_karatsuba_channel_sums sums; ok (qArray q)) := by
  simp [NDD_Reference.channels_ref,field.qm31_from_karatsuba_channel_sums,
    reconstruct,cadd,csub,byr,qArray,Array.index_usize,Array.make]
  simp [cArray,Array.index_usize,Array.make]
#print axioms cadd
#print axioms csub
#print axioms byr
#print axioms channels
end NDD_Channels
