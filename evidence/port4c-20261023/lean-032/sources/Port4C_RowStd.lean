import Port4C_QueryStd
import Port3_NativeRowLoop

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_RowStd
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 Port3_NativeQueryBody
abbrev K := aspis_core.field.QM31
abbrev E := aspis_core.field.wide_exact.WideExact
abbrev M := aspis_core.field.M31

def zeroK : K := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
def fromK (q : K) : E := ⟨q,zeroK⟩
def fromM (m : M) : E := fromK ⟨⟨m,0#u32⟩,⟨0#u32,0#u32⟩⟩

def install (ops : Ops) : Ops :=
  {Port3_NativeRowFrame.install (Port4C_QueryStd.install ops) with
    op1 := fun q => ok (fromK q)
    op10 := fun m => ok (fromM m)
    op12 := Slice.index_usize
    op13 := Array.index_usize
    op15 := fun _ _ _ => ok ()}

/-- One current emitted row with concrete std/read/embedding leaves. Trace
offsets still execute their total wrapping operations and cannot reject. -/
theorem step (ops : Ops) (v : alloc.vec.Vec K) (power : K)
    (next width : Usize) (basis : Array M 256#usize)
    (iter iter1 : core.ops.range.Range Usize) (b bout : verifier.BatchedWeights)
    (j : Usize) (m : M) (q : K)
    (hi : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some j,iter1))
    (hm : Array.index_usize basis j=ok m)
    (hq : Slice.index_usize v.deref j=ok q)
    (hp : Port3_NativeRowFrame.push b j power m=ok bout) :
    verifier.accumulate_batched_with_node_loop1.body (install ops)
      v power next width basis iter b=ok (cont (iter1,bout)) := by
  unfold verifier.accumulate_batched_with_node_loop1.body
  rw [hi,bind_tc_ok]
  simp only [install,Port3_NativeRowFrame.install,hm,hp,lift,bind_tc_ok,hq]

/-- Both std-array reads are actual physical reads, not arbitrary callbacks. -/
theorem reads (ops : Ops) :
    (install ops).op12=(@Slice.index_usize K) ∧
    (install ops).op13=(@Array.index_usize M 256#usize) ∧
    (install ops).op14=Port3_NativeRowFrame.push := ⟨rfl,rfl,rfl⟩

#print axioms step
#print axioms reads
end AspisR1.Port4C_RowStd
end
