import Port5Q1_ListCells
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_GeometryBinding
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeGeometryBody
abbrev FP := ZMod AspisCircleGroupOrder.P

def queryAt (queries : Array U32 22#usize) (i : Nat) : U32 := queries.val[i]?.getD 0#u32
def lane (a : Array U32 5#usize) (j : Fin 5) : U32 := a.val[j.val]?.getD 0#u32

def forQuery (geometry : verifier.QueryGeometry) (i : Usize) : Result (Array U32 5#usize) :=
  alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array U32 5#usize))
    geometry.inverses (Usize.wrapping_sub i geometry.start)

structure Binding (queries : Array U32 22#usize) (start end1 : Usize)
    (geometry : verifier.QueryGeometry) : Prop where
  start_eq : geometry.start=start
  order : start.val<end1.val
  bound : end1.val≤22
  line_size : geometry.line_z.val.length=end1.val-start.val
  inverse_size : geometry.inverses.val.length=end1.val-start.val
  line : ∀ i, i<end1.val-start.val →
    S7JoinBasisMachine.decode (geometry.line_z.val[i]?.getD 0#u32)=
      Port5Q1_Domain.lineZ (queryAt queries (start.val+i)).val
  inverses : ∀ i, i<end1.val-start.val → ∀ j : Fin 5,
    S7JoinBasisMachine.decode (lane (geometry.inverses.val[i]?.getD
      (Array.make 5#usize [0#u32,0#u32,0#u32,0#u32,0#u32])) j)=
      ((Port5Q1_Domain.words (queryAt queries (start.val+i)).val)[j.val]?.getD 0)⁻¹

end AspisR1.Port5Q1_GeometryBinding
end
