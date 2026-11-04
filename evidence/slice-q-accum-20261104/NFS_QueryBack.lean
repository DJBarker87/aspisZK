import NFS_QueryOps
import NFP_TraceBack
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFS_QueryBack
open Aeneas Aeneas.Std Result AspisR1Stage2 NFP_QueryCuts NFP_TraceTypes
open Port3_NativeQueryBody

def back (base : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
 (inverse : Inverse) (values : Dots) : Result Out := do
 let ops := NFS_QueryOps.installed base
 let alpha ← Array.index_usize p.alpha 1#usize
 let folded ← ops.op16 alpha values inverse
 let index ← lift (Usize.wrapping_mul 2#usize a.next)
 let tag ← lift (Usize.wrapping_add index 1#usize)
 ops.op15 10#u16 tag folded
 let offset ← lift (Usize.wrapping_sub a.next geometry.start)
 let z ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) geometry.line_z offset
 let square ← ops.op7 z z
 let doubled ← ops.op8 square
 let one ← ops.op5
 let node ← ops.op6 doubled one
 let (after,b) ← NFS_AccumInstall.run p a node folded pending
 ops.op19 none (.Query a.next)
 ok (.Ok (after,b))

/-- The accumulation reply is the CLOSED child's result on the exact same
line output, node and original owned prestate, including every Result branch. -/
theorem installed (base : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
 (inverse : Inverse) (values : Dots) (input : NFS_AccumDomain.Input p a pending) :
 back base p a geometry pending inverse values =
 NFP_SuffixCuts.back (NFS_QueryOps.installed base) p a geometry pending inverse values := by
 unfold back NFP_SuffixCuts.back
 simp only [NFS_QueryOps.line]
 congr 1
 funext alpha
 cases h : SAQ_LineQuery.line alpha values inverse with
 | fail error => simp only [h,bind_tc_fail]
 | div => simp only [h,bind_tc_div]
 | ok folded =>
  have canonical := NFS_AccumDomain.line alpha values inverse folded h
  have child := fun node => (NFS_AccumInstall.installed (NFS_QueryOps.base base)
   p a node folded pending input canonical).trans (NFS_QueryOps.accumulation base p a node folded pending).symm
  simp only [h,bind_tc_ok]
  simp only [child]
#print axioms installed
end AspisR1.NFS_QueryBack
end
