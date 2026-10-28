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
   simpa only [progress.2.1] using lt
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
   simpa only [←progress.1] using sweep t iter.start.val b progress
 obtain ⟨iter1,row,run,start,finish,inv1⟩ := NBF_RowInstall.body ops v q next basis iter b x
   width active v64 inv get hq hb
 let b1 : verifier.BatchedWeights := {b with raw:=b.raw.set iter.start row}
 have pc : S7JoinRowsTrace.Progress t (iter.start.val+1) (Port3_RowsInstall.toBW b1) := by
   refine ⟨progress.1,?_,?_⟩
   · change (b.raw.val.set iter.start.val row).length=64
     rw [List.length_set];exact progress.2.1
   · intro j hj
     by_cases same : j=iter.start.val
     · subst j
       have get1 : b1.raw.val[iter.start.val]?=some row := by
         change (b.raw.val.set iter.start.val row)[iter.start.val]?=some row
         rw [List.getElem?_set_self (by have:=progress.2.1;change b.raw.val.length=64 at this;omega)]
       -- The updated row always has four words; obtain its coordinate map.
       let y : Fin 4 → U64 := fun k=>row.val[k.val]'(by simpa [row.property] using k.isLt)
       have rebuild : makeRow y=row := by
         apply Subtype.ext
         apply List.ext_getElem
         · simp [makeRow,Array.make,row.property]
         · intro i h1 h2
           have hi : i<4 := by simpa only [row.property] using h2
           interval_cases i <;> rfl
       refine ⟨y,by simpa only [rebuild] using get1,?_⟩
       have bounds := inv1 iter.start.val row get1
       intro k
       have mem : y k∈row.val := List.getElem_mem _
       have hword := bounds (y k) mem
       simpa only [←progress.1,show iter.start.val<iter.start.val+1 by omega,if_true] using hword
     · obtain ⟨y,old,oldphase⟩ := progress.2.2 j hj
       refine ⟨y,?_,?_⟩
       · change (b.raw.val.set iter.start.val row)[j]?=some (makeRow y)
         rw [List.getElem?_set_ne (by omega)];exact old
       · have eq : (j<iter.start.val+1)↔j<iter.start.val := by omega
         simpa only [eq] using oldphase
 exact ⟨iter1,b1,run,start,finish,by simpa only [start] using pc⟩
#print axioms sweep
#print axioms body
end NBF_Progress
