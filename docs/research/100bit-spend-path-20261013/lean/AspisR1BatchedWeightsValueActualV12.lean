import AspisR1BatchedWeightsExtraction.Funs
import AspisR1BatchedAllPrefix
import BatchedWeightsActualReducer
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1BatchedWeightsValueActualV12
open AspisR1BatchedWeightsExtraction
abbrev RawVec := alloc.vec.Vec (Array Std.U64 4#usize)
abbrev Q := aspis_core.field.QM31
abbrev M := aspis_core.field.M31
def qOf (a b c d : M) : Q := { c0 := { a := a, b := b }, c1 := { a := c, b := d } }
theorem value_entry_four_reads
    (raw : RawVec) (terms index : Usize)
    (lane : Array Std.U64 4#usize)
    (x0 x1 x2 x3 : Std.U64) (m0 m1 m2 m3 : M)
    (hvec : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw index = .ok lane)
    (h0 : Array.index_usize lane 0#usize = .ok x0)
    (h1 : Array.index_usize lane 1#usize = .ok x1)
    (h2 : Array.index_usize lane 2#usize = .ok x2)
    (h3 : Array.index_usize lane 3#usize = .ok x3)
    (r0 : aspis_core.field.M31.reduce_u64 x0 = .ok m0)
    (r1 : aspis_core.field.M31.reduce_u64 x1 = .ok m1)
    (r2 : aspis_core.field.M31.reduce_u64 x2 = .ok m2)
    (r3 : aspis_core.field.M31.reduce_u64 x3 = .ok m3) :
    batched_weights.value_entry raw terms index = .ok (qOf m0 m1 m2 m3) := by
  simp only [batched_weights.value_entry, batched_weights.BatchedWeights.value, bind_tc_ok, hvec]
  simp only [h0, h1, h2, h3, r0, r1, r2, r3, bind_tc_ok]
  simp [Array.index_usize, Array.make, qOf]
#print axioms value_entry_four_reads
end AspisR1BatchedWeightsValueActualV12
