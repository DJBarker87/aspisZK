import NBF_BasisDomain
import NBF_FirstRows
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBF_Accumulate
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- Composition changes only the explicitly named basis/row callbacks. -/
def install (ops : Ops) : Ops := NBF_RowInstall.install (NBF_BasisInstall.install ops)

/-- SAME basis and row results are constructed from the reached accumulator.
The remaining rhs/power callbacks and final counter updates stay in source order. -/
theorem rows (ops : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (node : U32) (value : Stage2E) (b : verifier.BatchedWeights)
 (size : a.weights.val.length=64)
 (progress : S7JoinRowsTrace.Progress b.terms.val 0 (Port3_RowsInstall.toBW b))
 (hq : ∀ k, (S7Kani2OwnedRowRefinement.powerLimb (Port3_RowsInstall.toK a.power) k).val<2^31-1) :
 ∃ basis mid,
 NBF_BasisDomain.source ops node=ok basis ∧
 verifier.accumulate_batched_with_node_loop1 (install ops)
   {start:=0#usize,«end»:=64#usize} a.weights a.power a.next b 64#usize basis=ok mid ∧
 mid.terms=b.terms ∧ mid.raw.val.length=64 ∧
 (∀ (j : Nat) (row : NBF_Frame.Row), mid.raw.val[j]?=some row → NBB_Sweep.Bound (b.terms.val+1) row) ∧
 verifier.accumulate_batched_with_node (install ops) p a node value b=
   (do let term ← lift (Usize.wrapping_add mid.terms 1#usize)
       let product ← ops.op3 value a.power
       let rhs ← ops.op2 a.rhs product
       (install ops).op15 11#u16 a.next rhs
       let power ← ops.op9 a.power p.rho
       let next ← lift (Usize.wrapping_add a.next 1#usize)
       ok ({a with rhs:=rhs,power:=power,next:=next},{mid with terms:=term})) := by
 obtain ⟨basis,hbasis,hcanonical⟩ := NBF_BasisDomain.total ops node
 have hb : ∀ j : Usize, j.val<64 → ∀ m, Array.index_usize basis j=ok m → m.val<2^31-1 := by
   intro j bound m read
   exact NBF_BasisDomain.read_canonical ops node basis hbasis j (by omega) m read
 obtain ⟨mid,run,terms,len,phase⟩ := NBF_RowsTotal.full (NBF_BasisInstall.install ops)
   a.weights a.power a.next basis b size progress hq hb
 refine ⟨basis,mid,hbasis,run,terms,len,phase,?_⟩
 have width : alloc.vec.Vec.len a.weights=64#usize := UScalar.eq_of_val_eq size
 have produced :
   (do let m ← (install ops).op4
       let initial := Array.repeat 256#usize m
       let one ← (install ops).op5
       let initialized ← Array.update initial 0#usize one
       verifier.accumulate_batched_with_node_loop0 (install ops) one node 64#usize initialized 1#usize)=ok basis := by
   change NBF_BasisDomain.source (NBF_RowInstall.install ops) node=ok basis
   rw [NBF_BasisDomain.association]
   rw [NBF_BasisDomain.association] at hbasis
   exact hbasis
 unfold verifier.accumulate_batched_with_node
 rw [width]
 -- Collapse only the constructor/basis prefix, preserving each source tail bind.
 change (do
   let basis ← (do let m ← (install ops).op4
                   let initial := Array.repeat 256#usize m
                   let one ← (install ops).op5
                   let initialized ← Array.update initial 0#usize one
                   verifier.accumulate_batched_with_node_loop0 (install ops) one node 64#usize initialized 1#usize)
   let mid ← verifier.accumulate_batched_with_node_loop1 (install ops)
     {start:=0#usize,«end»:=64#usize} a.weights a.power a.next b 64#usize basis
   _) = _
 rw [produced,bind_tc_ok,run,bind_tc_ok]
 rfl
#print axioms rows
end NBF_Accumulate
