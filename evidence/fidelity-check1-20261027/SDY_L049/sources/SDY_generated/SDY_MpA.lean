import SDY_MpASteps
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace SDY_MpA
open SDY_Join_Release AspisR1.AdapterRw.Scalar


theorem parent : multiproof.verify_in_place_loop0_loop0.body hash () 1#usize nodes .Eight idx val 0#usize 0#usize 0#usize none = ok (.cont (.Eight,outidx,outval,224#usize,1#usize,1#usize,none)) := by
  unfold multiproof.verify_in_place_loop0_loop0.body
  change (do let r ← multiproof.verify_in_place_loop0_loop0_loop0 (it 0#usize) id idx val 1#usize nodes 0#usize 0#usize 1#u32 none; let (a,i,p,b) := r; match p with
    | none => do
      let d ← aspis_core.r0.merkle.parent_with_digest hash () (Array.from_slice children b.iter.slice)
      let idx1 ← Array.update idx 0#usize 1#u32
      let val1 ← Array.update val 0#usize d
      let w ← 0#usize + 1#usize
      ok (.cont (.Eight,idx1,val1,a,w,i,none))
    | some _ => ok (.done (.Eight,idx,val,1#usize,a,p,0#u32))) = _
  rw [inner]
  rfl
#print axioms parent
abbrev PState := multiproof.Arity × Array U32 16#usize × Array Node 16#usize × Usize × Usize × Usize × Option Bool
def pstep (s : PState) := multiproof.verify_in_place_loop0_loop0.body hash () 1#usize nodes s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.2.2.2.2.2
theorem pstep_eq (a : multiproof.Arity) (x : Array U32 16#usize) (v : Array Node 16#usize) (offset w i : Usize) (p : Option Bool) :
    pstep (a,x,v,offset,w,i,p) = multiproof.verify_in_place_loop0_loop0.body hash () 1#usize nodes a x v offset w i p := rfl
#print axioms pstep_eq
theorem pend : pstep (.Eight,outidx,outval,224#usize,1#usize,1#usize,none) = ok (.done (.Eight,outidx,outval,1#usize,224#usize,none,1#u32)) := by rfl
#print axioms pend
theorem prunEnd : loop pstep (.Eight,outidx,outval,224#usize,1#usize,1#usize,none) = ok (.Eight,outidx,outval,1#usize,224#usize,none,1#u32) := by
  exact SDY_Loop.done pstep _ _ pend
#print axioms prunEnd
theorem prun : multiproof.verify_in_place_loop0_loop0 hash () .Eight idx val 1#usize nodes 0#usize 0#usize 0#usize none = ok (.Eight,outidx,outval,1#usize,224#usize,none,1#u32) := by
  exact SDY_Loop.next pstep _ _ _ ((pstep_eq .Eight idx val 0#usize 0#usize 0#usize none).trans parent) prunEnd
#print axioms prun

def rejectStep (s : State) := body outidx outval 1#usize nodes 0#u32 none s.1 s.2.1 s.2.2.1 s.2.2.2
theorem rejectStep_eq (iter : Iter) (b : Back) (offset i : Usize) :
    rejectStep (iter,b,offset,i) = body outidx outval 1#usize nodes 0#u32 none iter b offset i := rfl
#print axioms rejectStep_eq
theorem rejectBody : body outidx outval 1#usize nodes 0#u32 none (it 0#usize) id 224#usize 0#usize = ok (.done (224#usize,0#usize,some false,it 1#usize)) := by
  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  rw [add_eq 0#usize 1#usize 1#usize rfl,add_eq 224#usize 32#usize 256#usize rfl]
  simp only [bind_tc_ok]
  have hn : core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8) nodes {start:=224#usize,«end»:=256#usize} = ok none := by
    simp [core.slice.Slice.get,core.slice.index.SliceIndexRangeUsizeSlice,core.slice.index.SliceIndexRangeUsizeSlice.get,nodes,SDY_Slice.nodes,Slice.length]
  simp [multiproof.index_at,outidx]
  rw [hn]
  rfl
#print axioms rejectBody
theorem rejectInner : multiproof.verify_in_place_loop0_loop0_loop0 (it 0#usize) id outidx outval 1#usize nodes 224#usize 0#usize 0#u32 none = ok (224#usize,0#usize,some false,it 1#usize) := by
  exact SDY_Loop.done rejectStep _ _ ((rejectStep_eq (it 0#usize) id 224#usize 0#usize).trans rejectBody)
#print axioms rejectInner
theorem rejectParent : multiproof.verify_in_place_loop0_loop0.body hash () 1#usize nodes .Eight outidx outval 224#usize 0#usize 0#usize none = ok (.done (.Eight,outidx,outval,1#usize,224#usize,some false,0#u32)) := by
  unfold multiproof.verify_in_place_loop0_loop0.body
  change (do let (a,i,p,b) ← multiproof.verify_in_place_loop0_loop0_loop0 (it 0#usize) id outidx outval 1#usize nodes 224#usize 0#usize 0#u32 none
             match p with
             | none => do
               let d ← aspis_core.r0.merkle.parent_with_digest hash () (Array.from_slice children b.iter.slice)
               let idx1 ← Array.update outidx 0#usize 0#u32
               let val1 ← Array.update outval 0#usize d
               let w ← 0#usize + 1#usize
               ok (.cont (.Eight,idx1,val1,a,w,i,none))
             | some _ => ok (.done (.Eight,outidx,outval,1#usize,a,p,0#u32))) = _
  rw [rejectInner];rfl
#print axioms rejectParent
theorem rejectLevel : multiproof.verify_in_place_loop0_loop0 hash () .Eight outidx outval 1#usize nodes 224#usize 0#usize 0#usize none = ok (.Eight,outidx,outval,1#usize,224#usize,some false,0#u32) := by
  exact SDY_Loop.done pstep _ _ ((pstep_eq .Eight outidx outval 224#usize 0#usize 0#usize none).trans rejectParent)
#print axioms rejectLevel
abbrev OState := core.ops.range.Range U32 × multiproof.Arity × Array U32 16#usize × Array Node 16#usize × Usize × Usize × Option Bool
def ostep (s : OState) := multiproof.verify_in_place_loop0.body hash () (node 0#u8) nodes s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.2.2.2.2.2
theorem outerFirst : ostep ({start:=0#u32,«end»:=6#u32},.Eight,idx,val,1#usize,0#usize,none) = ok (.cont ({start:=1#u32,«end»:=6#u32},.Eight,outidx,outval,1#usize,224#usize,none)) := by
  unfold ostep multiproof.verify_in_place_loop0.body
  change (do let (a,x,v,n,offset,p,i) ← multiproof.verify_in_place_loop0_loop0 hash () .Eight idx val 1#usize nodes 0#usize 0#usize 0#usize none
             match i with
             | 1#uscalar => ok (ControlFlow.cont ({start:=1#u32,«end»:=6#u32},a,x,v,n,offset,p))
             | _ => match p with
               | none => ok (ControlFlow.done (x,v,none))
               | some _ => ok (ControlFlow.done (x,v,p))) = _
  rw [prun];rfl
#print axioms outerFirst
theorem outerLast : ostep ({start:=1#u32,«end»:=6#u32},.Eight,outidx,outval,1#usize,224#usize,none) = ok (.done (outidx,outval,some false)) := by
  unfold ostep multiproof.verify_in_place_loop0.body
  change (do let (a,x,v,n,offset,p,i) ← multiproof.verify_in_place_loop0_loop0 hash () .Eight outidx outval 1#usize nodes 224#usize 0#usize 0#usize none
             match i with
             | 1#uscalar => ok (ControlFlow.cont ({start:=2#u32,«end»:=6#u32},a,x,v,n,offset,p))
             | _ => match p with
               | none => ok (ControlFlow.done (x,v,none))
               | some _ => ok (ControlFlow.done (x,v,p))) = _
  rw [rejectLevel];rfl
#print axioms outerLast
theorem orunLast : loop ostep ({start:=1#u32,«end»:=6#u32},.Eight,outidx,outval,1#usize,224#usize,none) = ok (outidx,outval,some false) := by
  exact SDY_Loop.done ostep _ _ outerLast
#print axioms orunLast
theorem orun : multiproof.verify_in_place_loop0 hash {start:=0#u32,«end»:=6#u32} () .Eight (node 0#u8) idx val 1#usize nodes 0#usize none = ok (outidx,outval,some false) := by
  exact SDY_Loop.next ostep _ _ _ outerFirst orunLast
#print axioms orun
def singleton : Slice U32 := ⟨[8#u32],by scalar_tac⟩
theorem formed : multiproof.well_formed singleton = ok true := by
  unfold multiproof.well_formed
  simp [singleton,multiproof.MAX_BATCH,core.slice.Slice.is_empty,core.slice.Slice.windows]
  unfold core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.all core.iter.traits.iterator.Iterator.all.default
  rw [loop.eq_def]
  simp [core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next,singleton]
  unfold core.slice.Slice.iter
  simp only [bind_tc_ok]
  unfold core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all core.iter.traits.iterator.Iterator.all.default
  rw [loop.eq_def]
  simp [core.slice.iter.IteratorSliceIter.next,singleton,multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut,multiproof.LEAF_BITS]
  rw [loop.eq_def]
  rfl
#print axioms formed

theorem emitted : multiproof.verify_in_place hash () .Eight (node 0#u8) idx val 1#usize nodes = ok (false,outidx,outval) := by
  unfold multiproof.verify_in_place
  simp only [multiproof.MAX_BATCH]
  change (do let b ← multiproof.well_formed singleton
             if b then do
               let (x,v,p) ← multiproof.verify_in_place_loop0 hash {start:=0#u32,«end»:=6#u32} () .Eight (node 0#u8) idx val 1#usize nodes 0#usize none
               match p with
               | none => fail .panic
               | some b => ok (b,x,v)
             else ok (false,idx,val)) = _
  rw [formed]
  simp only [bind_tc_ok,ite_true]
  rw [orun]
  rfl
#print axioms emitted
end SDY_MpA
