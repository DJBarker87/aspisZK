import NBF_RowInstall
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBF_Progress
open AspisR1 AspisR1Stage2
open S7Kani2OwnedRowRefinement (makeRow)
/-- The inherited source progress invariant supplies the local raw-vector
cursor invariant, with no additional per-row phase assumption. -/
theorem sweep (t cursor : Nat) (b : verifier.BatchedWeights)
 (progress : S7JoinRowsTrace.Progress t cursor (Port3_RowsInstall.toBW b)) :
 NBB_Sweep.Inv t cursor b.raw := by
 intro j row read
 have hj : j<64 := by
   have lt := (List.getElem?_eq_some_iff.mp read).1
   have size : b.raw.val.length=64 := progress.2.1
   omega
 obtain ⟨x,get,phase⟩ := progress.2.2 j hj
 have eq : row=makeRow x := Option.some.inj (read.symm.trans get)
 subst row
 intro word mem
 simp only [makeRow,Array.make,List.mem_cons,List.not_mem_nil,or_false] at mem
 rcases mem with rfl|rfl|rfl|rfl <;> exact phase _

/-- Every local direct native-body call gets its exact phase/read domain
from the inherited SAME progress witness. Its successor progress is derived. -/
theorem body (ops : Port3_NativeQueryBody.Ops) (v : alloc.vec.Vec NBF_RowInstall.Q)
 (q : NBF_RowInstall.Q) (next : Usize) (basis : Array U32 256#usize)
 (iter : core.ops.range.Range Usize) (b : verifier.BatchedWeights)
 (t : Nat) (width : iter.end.val=64) (active : iter.start.val<64)
 (v64 : v.val.length=64)
 (progress : S7JoinRowsTrace.Progress t iter.start.val (Port3_RowsInstall.toBW b))
 (hq : ∀ k, (S7Kani2OwnedRowRefinement.powerLimb (Port3_RowsInstall.toK q) k).val<2^31-1)
 (hb : ∀ j : Usize, j.val<64 → ∀ m, Array.index_usize basis j=ok m → m.val<2^31-1) :
 ∃ iter1 b1,
 Port3_NativeQueryBody.verifier.accumulate_batched_with_node_loop1.body
   (NBF_RowInstall.install ops) v q next 64#usize basis iter b=
   ok (ControlFlow.cont (iter1,b1)) ∧
 iter1.start.val=iter.start.val+1 ∧ iter1.end=iter.end ∧
 S7JoinRowsTrace.Progress t iter1.start.val (Port3_RowsInstall.toBW b1) := by
 obtain ⟨x,get,phase⟩ := progress.2.2 iter.start.val active
 have inv : NBB_Sweep.Inv b.terms.val iter.start.val b.raw := by
   have terms : b.terms.val=t := progress.1
   rw [terms];exact sweep t iter.start.val b progress
 obtain ⟨iter1,row,run,start,finish,inv1⟩ := NBF_RowInstall.body ops v q next basis iter b x
   width active v64 inv get hq hb
 let b1 : verifier.BatchedWeights := {b with raw:=b.raw.set iter.start row}
 let y : Fin 4 → U64 := fun k=>row.val[k.val]'(by simpa [row.property] using k.isLt)
 have rebuild : makeRow y=row := by
   apply Subtype.ext
   apply List.ext_getElem
   · simp [makeRow,Array.make,row.property]
   · intro i h1 h2
     have hi : i<4 := by have len := row.property;change row.val.length=4 at len;omega
     interval_cases i <;> rfl
 have get1 : (b.raw.set iter.start row).val[iter.start.val]?=some row := by
   change (b.raw.val.set iter.start.val row)[iter.start.val]?=some row
   rw [List.getElem?_set_self (by have size : b.raw.val.length=64 := progress.2.1;omega)]
 have done : ∀ k, S7Kani3PhaseInvariant.Phase (t+1) (y k).val := by
   intro k
   have bounds := inv1 iter.start.val row get1 (y k) (List.getElem_mem _)
   have terms : b.terms.val=t := progress.1
   simpa [terms,NBB_Phase.Bound,S7Kani3PhaseInvariant.Phase,
     AspisR1BatchedFoldSourceStep.productCap] using bounds
 have pc : S7JoinRowsTrace.Progress t (iter.start.val+1) (Port3_RowsInstall.toBW b1) := by
   have written := S7JoinRowsTrace.progress_write t iter.start.val (Port3_RowsInstall.toBW b)
     y iter.start rfl active progress done
   change S7JoinRowsTrace.Progress t (iter.start.val+1)
     {Port3_RowsInstall.toBW b with raw:=b.raw.set iter.start row}
   simpa only [rebuild,Port3_RowsInstall.toBW] using written
 exact ⟨iter1,b1,run,start,finish,by simpa only [start] using pc⟩
#print axioms sweep
#print axioms body
end NBF_Progress
