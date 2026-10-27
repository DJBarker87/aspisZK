import SDY_MpBSteps
import SDY_MpCSteps
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace SDY_MpB
open SDY_Join_Release AspisR1.AdapterRw.Scalar


theorem digest_result : aspis_core.r0.merkle.parent_with_digest hash () (Array.from_slice children (fin0 id (it 8#usize)).iter.slice) = ok (node 3#u8) := by
  unfold aspis_core.r0.merkle.parent_with_digest SDY_Join_digest
  split
  · rfl
  · rename_i h
    exfalso
    apply h
    scalar_tac
#print axioms digest_result

theorem parent : multiproof.verify_in_place_loop0_loop0.body hash () 1#usize nodes .Eight idx val 0#usize 0#usize 0#usize none = ok (ControlFlow.cont (multiproof.Arity.Eight,outidx,outval,224#usize,1#usize,1#usize,none)) := by
  unfold multiproof.verify_in_place_loop0_loop0.body
  change (do let r ← multiproof.verify_in_place_loop0_loop0_loop0 (it 0#usize) id idx val 1#usize nodes 0#usize 0#usize 1#u32 none; let (a,i,p,b) := r; match p with
    | none => do
      let d ← aspis_core.r0.merkle.parent_with_digest hash () (Array.from_slice children b.iter.slice)
      let idx1 ← Array.update idx 0#usize 1#u32
      let val1 ← Array.update val 0#usize d
      let w ← 0#usize + 1#usize
      ok (ControlFlow.cont (multiproof.Arity.Eight,idx1,val1,a,w,i,none))
    | some _ => ok (ControlFlow.done (multiproof.Arity.Eight,idx,val,1#usize,a,p,0#u32))) = _
  rw [inner]
  simp only [bind_tc_ok]
  rw [add_eq 0#usize 1#usize 1#usize rfl,digest_result]
  rfl
#print axioms parent
abbrev PState := multiproof.Arity × Array U32 16#usize × Array Node 16#usize × Usize × Usize × Usize × Option Bool
def pstep (s : PState) := multiproof.verify_in_place_loop0_loop0.body hash () 1#usize nodes s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.2.2.2.2.2
theorem pstep_eq (a : multiproof.Arity) (x : Array U32 16#usize) (v : Array Node 16#usize) (offset w i : Usize) (p : Option Bool) :
    pstep (a,x,v,offset,w,i,p) = multiproof.verify_in_place_loop0_loop0.body hash () 1#usize nodes a x v offset w i p := rfl
#print axioms pstep_eq
theorem pend : pstep (multiproof.Arity.Eight,outidx,outval,224#usize,1#usize,1#usize,none) = ok (ControlFlow.done (multiproof.Arity.Eight,outidx,outval,1#usize,224#usize,none,1#u32)) := by rfl
#print axioms pend
theorem prunEnd : loop pstep (multiproof.Arity.Eight,outidx,outval,224#usize,1#usize,1#usize,none) = ok (multiproof.Arity.Eight,outidx,outval,1#usize,224#usize,none,1#u32) := by
  exact SDY_Loop.done pstep _ _ pend
#print axioms prunEnd
theorem prun : multiproof.verify_in_place_loop0_loop0 hash () .Eight idx val 1#usize nodes 0#usize 0#usize 0#usize none = ok (multiproof.Arity.Eight,outidx,outval,1#usize,224#usize,none,1#u32) := by
  exact SDY_Loop.next pstep _ _ _ ((pstep_eq .Eight idx val 0#usize 0#usize 0#usize none).trans parent) prunEnd
#print axioms prun

def rejectStep (s : State) := body outidx outval 1#usize nodes 0#u32 none s.1 s.2.1 s.2.2.1 s.2.2.2
theorem rejectStep_eq (iter : Iter) (b : Back) (offset i : Usize) :
    rejectStep (iter,b,offset,i) = body outidx outval 1#usize nodes 0#u32 none iter b offset i := rfl
#print axioms rejectStep_eq
theorem rejectBody : body outidx outval 1#usize nodes 0#u32 none (it 0#usize) id 224#usize 0#usize = ok (ControlFlow.done (224#usize,0#usize,some false,it 1#usize)) := by
  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  rw [add_eq 0#usize 1#usize 1#usize rfl,add_eq 224#usize 32#usize 256#usize rfl]
  simp only [bind_tc_ok]
  have hn : core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8) nodes {start:=224#usize,«end»:=256#usize} = ok none := by
    unfold core.slice.Slice.get core.slice.index.SliceIndexRangeUsizeSlice core.slice.index.SliceIndexRangeUsizeSlice.get
    simp only [nodes,SDY_Slice.nodes,Slice.length,List.length_replicate]
    rfl
  have hi : multiproof.index_at outidx 0#usize = ok 1#u32 := by rfl
  have hs : 1#u32 >>> 3#i32 = ok 0#u32 := by rfl
  have hm : 1#u32 &&& 7#u32 = 1#u32 := by rfl
  have hc : UScalar.cast .Usize 1#u32 = 1#usize := by scalar_tac
  rw [hi,bind_tc_ok,hs,bind_tc_ok]
  simp only [if_pos rfl,hm,hc,lift,bind_tc_ok]
  simp only [if_neg (by decide : 1#usize ≠ 0#usize)]
  rw [hn]
  rfl
#print axioms rejectBody
theorem rejectInner : multiproof.verify_in_place_loop0_loop0_loop0 (it 0#usize) id outidx outval 1#usize nodes 224#usize 0#usize 0#u32 none = ok (224#usize,0#usize,some false,it 1#usize) := by
  exact SDY_Loop.done rejectStep _ _ ((rejectStep_eq (it 0#usize) id 224#usize 0#usize).trans rejectBody)
#print axioms rejectInner
theorem rejectParent : multiproof.verify_in_place_loop0_loop0.body hash () 1#usize nodes .Eight outidx outval 224#usize 0#usize 0#usize none = ok (ControlFlow.done (multiproof.Arity.Eight,outidx,outval,1#usize,224#usize,some false,0#u32)) := by
  unfold multiproof.verify_in_place_loop0_loop0.body
  change (do let (a,i,p,b) ← multiproof.verify_in_place_loop0_loop0_loop0 (it 0#usize) id outidx outval 1#usize nodes 224#usize 0#usize 0#u32 none
             match p with
             | none => do
               let d ← aspis_core.r0.merkle.parent_with_digest hash () (Array.from_slice children b.iter.slice)
               let idx1 ← Array.update outidx 0#usize 0#u32
               let val1 ← Array.update outval 0#usize d
               let w ← 0#usize + 1#usize
               ok (ControlFlow.cont (multiproof.Arity.Eight,idx1,val1,a,w,i,none))
             | some _ => ok (ControlFlow.done (multiproof.Arity.Eight,outidx,outval,1#usize,a,p,0#u32))) = _
  rw [rejectInner];rfl
#print axioms rejectParent
theorem rejectLevel : multiproof.verify_in_place_loop0_loop0 hash () .Eight outidx outval 1#usize nodes 224#usize 0#usize 0#usize none = ok (multiproof.Arity.Eight,outidx,outval,1#usize,224#usize,some false,0#u32) := by
  exact SDY_Loop.done pstep _ _ ((pstep_eq .Eight outidx outval 224#usize 0#usize 0#usize none).trans rejectParent)
#print axioms rejectLevel
abbrev OState := core.ops.range.Range U32 × multiproof.Arity × Array U32 16#usize × Array Node 16#usize × Usize × Usize × Option Bool
def ostep (s : OState) := multiproof.verify_in_place_loop0.body hash () (node 0#u8) nodes s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.2.2.2.2.2
theorem range_next (i j : U32) (lt : i.val < 6) (inc : j.val = i.val+1) :
    core.iter.range.IteratorRange.next core.iter.range.StepU32 {start:=i,«end»:=6#u32} = ok (some i,{start:=j,«end»:=6#u32}) := by
  obtain ⟨v,hv,he⟩ := WP.spec_imp_exists (core.iter.range.IteratorRange.next_U32_some_spec {start:=i,«end»:=6#u32} lt)
  rcases v with ⟨o,r⟩
  rcases he with ⟨ho,hr,hend⟩
  have hs : r.start = j := UScalar.eq_imp r.start j (by change r.start.val = i.val+1 at hr; omega)
  have rr : r = {start:=j,«end»:=6#u32} := by cases r; simp_all
  simpa only [ho,rr] using hv
#print axioms range_next
theorem outerFirst : ostep ({start:=0#u32,«end»:=6#u32},.Eight,idx,val,1#usize,0#usize,none) = ok (ControlFlow.cont ({start:=1#u32,«end»:=6#u32},.Eight,outidx,outval,1#usize,224#usize,none)) := by
  unfold ostep multiproof.verify_in_place_loop0.body
  rw [range_next 0#u32 1#u32 (by decide) rfl,bind_tc_ok]
  change (do let (a,x,v,n,offset,p,i) ← multiproof.verify_in_place_loop0_loop0 hash () .Eight idx val 1#usize nodes 0#usize 0#usize 0#usize none
             match i with
             | 1#uscalar => ok (ControlFlow.cont (({start:=1#u32,«end»:=6#u32} : core.ops.range.Range U32),a,x,v,n,offset,p))
             | _ => match p with
               | none => ok (ControlFlow.done (x,v,none))
               | some _ => ok (ControlFlow.done (x,v,p))) = _
  rw [prun];rfl
#print axioms outerFirst
theorem outerLast : ostep ({start:=1#u32,«end»:=6#u32},.Eight,outidx,outval,1#usize,224#usize,none) = ok (ControlFlow.done (outidx,outval,some false)) := by
  unfold ostep multiproof.verify_in_place_loop0.body
  rw [range_next 1#u32 2#u32 (by decide) rfl,bind_tc_ok]
  change (do let (a,x,v,n,offset,p,i) ← multiproof.verify_in_place_loop0_loop0 hash () .Eight outidx outval 1#usize nodes 224#usize 0#usize 0#usize none
             match i with
             | 1#uscalar => ok (ControlFlow.cont (({start:=2#u32,«end»:=6#u32} : core.ops.range.Range U32),a,x,v,n,offset,p))
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
def singleton : Slice U32 := ⟨[9#u32],by scalar_tac⟩
abbrev Pred := multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool
abbrev PredCall := multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut
abbrev ReadIter := core.slice.iter.Iter U32
abbrev AllState := ReadIter × Unit
abbrev AllOut := Bool × ReadIter × Unit
def allBody : AllState → Result (ControlFlow AllState AllOut) :=
  fun (self',predicate') => do
    let (item,self'') ← (core.iter.traits.iterator.IteratorSliceIter U32).next self'
    match item with
    | none => ok (ControlFlow.done (true,self'',predicate'))
    | some value =>
      let (holds,predicate'') ← Pred.call_mut predicate' value
      if holds then ok (ControlFlow.cont (self'',predicate'')) else ok (ControlFlow.done (false,self'',predicate''))
theorem pred_result : PredCall () 9#u32 = ok (true,()) := by
  unfold PredCall multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut multiproof.LEAF_BITS
  rfl
#print axioms pred_result
theorem all_first : allBody (⟨singleton,0⟩,()) = ok (ControlFlow.cont (⟨singleton,1⟩,())) := by
  unfold allBody
  change (do let (b,p) ← PredCall () 9#u32; if b then ok (ControlFlow.cont ((⟨singleton,1⟩ : ReadIter),p)) else ok (ControlFlow.done (false,(⟨singleton,1⟩ : ReadIter),p))) = _
  rw [pred_result]
  rfl
#print axioms all_first
theorem all_last : allBody (⟨singleton,1⟩,()) = ok (ControlFlow.done (true,⟨singleton,1⟩,())) := by rfl
#print axioms all_last
theorem all_run_last : loop allBody (⟨singleton,1⟩,()) = ok (true,⟨singleton,1⟩,()) := SDY_Loop.done allBody _ _ all_last
#print axioms all_run_last
theorem all_run : loop allBody (⟨singleton,0⟩,()) = ok (true,⟨singleton,1⟩,()) := SDY_Loop.next allBody _ _ _ all_first all_run_last
#print axioms all_run
theorem all_result : core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all Pred ⟨singleton,0⟩ () = ok (true,⟨singleton,1⟩) := by
  have hh := congrArg (fun r : Result AllOut => do let out ← r; ok (out.1,out.2.1)) all_run
  unfold core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all core.iter.traits.iterator.Iterator.all.default
  convert hh using 1 <;> try rfl
  congr 2
  funext x
  rcases x with ⟨iter,pred⟩
  cases pred
  unfold allBody
  simp
  all_goals
    intro a b h
    cases a <;> simp
    all_goals
      intros
      split <;> rfl
#print axioms all_result
abbrev WinPred := multiproof.well_formed.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU32Bool
def windows : core.slice.iter.Windows U32 := ⟨singleton,2#usize,0⟩
theorem windows_result : core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.all WinPred windows () = ok (true,windows) := by
  unfold core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.all core.iter.traits.iterator.Iterator.all.default
  rw [loop.eq_def]
  rfl
#print axioms windows_result
theorem formed : multiproof.well_formed singleton = ok true := by
  unfold multiproof.well_formed multiproof.MAX_BATCH
  change (do let (b,_) ← core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.all WinPred windows ()
             if b then do
               let (b2,_) ← core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all Pred ⟨singleton,0⟩ ()
               ok b2
             else ok false) = _
  rw [windows_result,bind_tc_ok]
  simp only [ite_true]
  rw [all_result]
  rfl
#print axioms formed

theorem emitted : multiproof.verify_in_place hash () .Eight (node 0#u8) idx val 1#usize nodes = ok (false,outidx,outval) := by
  have hg : Slice.len nodes = 224#usize := by
    apply UScalar.eq_of_val_eq
    change (List.replicate 224 _).length = 224
    exact List.length_replicate
  have hm : 224#usize % 32#usize = ok 0#usize := by rfl
  have hl : multiproof.Arity.levels .Eight = ok 6#u32 := by
    unfold multiproof.Arity.levels multiproof.Arity.bits multiproof.LEAF_BITS
    rfl
  have hx : core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32)) idx {«end»:=1#usize} = ok singleton := by rfl
  unfold multiproof.verify_in_place
  simp only [multiproof.MAX_BATCH]
  simp only [show (1#usize = 0#usize) = False from propext (by decide),show (1#usize > 16#usize) = False from propext (by decide),ite_false]
  rw [hx,bind_tc_ok,formed,bind_tc_ok]
  simp only [ite_true]
  rw [hg,hm,bind_tc_ok]
  simp only [show (0#usize != 0#usize) = false from rfl, Bool.false_eq_true,ite_false]
  rw [hl,bind_tc_ok,orun]
  rfl
#print axioms emitted
end SDY_MpB
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace SDY_MpC
open SDY_Join_Release AspisR1.AdapterRw.Scalar


theorem digest_result : aspis_core.r0.merkle.parent_with_digest hash () (Array.from_slice children (fin0 id (it 8#usize)).iter.slice) = ok (node 4#u8) := by
  unfold aspis_core.r0.merkle.parent_with_digest SDY_Join_digest
  split
  · rfl
  · rename_i h
    exfalso
    apply h
    scalar_tac
#print axioms digest_result

theorem parent : multiproof.verify_in_place_loop0_loop0.body hash () 1#usize nodes .Eight idx val 0#usize 0#usize 0#usize none = ok (ControlFlow.cont (multiproof.Arity.Eight,outidx,outval,224#usize,1#usize,1#usize,none)) := by
  unfold multiproof.verify_in_place_loop0_loop0.body
  change (do let r ← multiproof.verify_in_place_loop0_loop0_loop0 (it 0#usize) id idx val 1#usize nodes 0#usize 0#usize 1#u32 none; let (a,i,p,b) := r; match p with
    | none => do
      let d ← aspis_core.r0.merkle.parent_with_digest hash () (Array.from_slice children b.iter.slice)
      let idx1 ← Array.update idx 0#usize 1#u32
      let val1 ← Array.update val 0#usize d
      let w ← 0#usize + 1#usize
      ok (ControlFlow.cont (multiproof.Arity.Eight,idx1,val1,a,w,i,none))
    | some _ => ok (ControlFlow.done (multiproof.Arity.Eight,idx,val,1#usize,a,p,0#u32))) = _
  rw [inner]
  simp only [bind_tc_ok]
  rw [add_eq 0#usize 1#usize 1#usize rfl,digest_result]
  rfl
#print axioms parent
abbrev PState := multiproof.Arity × Array U32 16#usize × Array Node 16#usize × Usize × Usize × Usize × Option Bool
def pstep (s : PState) := multiproof.verify_in_place_loop0_loop0.body hash () 1#usize nodes s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.2.2.2.2.2
theorem pstep_eq (a : multiproof.Arity) (x : Array U32 16#usize) (v : Array Node 16#usize) (offset w i : Usize) (p : Option Bool) :
    pstep (a,x,v,offset,w,i,p) = multiproof.verify_in_place_loop0_loop0.body hash () 1#usize nodes a x v offset w i p := rfl
#print axioms pstep_eq
theorem pend : pstep (multiproof.Arity.Eight,outidx,outval,224#usize,1#usize,1#usize,none) = ok (ControlFlow.done (multiproof.Arity.Eight,outidx,outval,1#usize,224#usize,none,1#u32)) := by rfl
#print axioms pend
theorem prunEnd : loop pstep (multiproof.Arity.Eight,outidx,outval,224#usize,1#usize,1#usize,none) = ok (multiproof.Arity.Eight,outidx,outval,1#usize,224#usize,none,1#u32) := by
  exact SDY_Loop.done pstep _ _ pend
#print axioms prunEnd
theorem prun : multiproof.verify_in_place_loop0_loop0 hash () .Eight idx val 1#usize nodes 0#usize 0#usize 0#usize none = ok (multiproof.Arity.Eight,outidx,outval,1#usize,224#usize,none,1#u32) := by
  exact SDY_Loop.next pstep _ _ _ ((pstep_eq .Eight idx val 0#usize 0#usize 0#usize none).trans parent) prunEnd
#print axioms prun

def rejectStep (s : State) := body outidx outval 1#usize nodes 0#u32 none s.1 s.2.1 s.2.2.1 s.2.2.2
theorem rejectStep_eq (iter : Iter) (b : Back) (offset i : Usize) :
    rejectStep (iter,b,offset,i) = body outidx outval 1#usize nodes 0#u32 none iter b offset i := rfl
#print axioms rejectStep_eq
theorem rejectBody : body outidx outval 1#usize nodes 0#u32 none (it 0#usize) id 224#usize 0#usize = ok (ControlFlow.done (224#usize,0#usize,some false,it 1#usize)) := by
  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  rw [add_eq 0#usize 1#usize 1#usize rfl,add_eq 224#usize 32#usize 256#usize rfl]
  simp only [bind_tc_ok]
  have hn : core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8) nodes {start:=224#usize,«end»:=256#usize} = ok none := by
    unfold core.slice.Slice.get core.slice.index.SliceIndexRangeUsizeSlice core.slice.index.SliceIndexRangeUsizeSlice.get
    simp only [nodes,SDY_Slice.nodes,Slice.length,List.length_replicate]
    rfl
  have hi : multiproof.index_at outidx 0#usize = ok 1#u32 := by rfl
  have hs : 1#u32 >>> 3#i32 = ok 0#u32 := by rfl
  have hm : 1#u32 &&& 7#u32 = 1#u32 := by rfl
  have hc : UScalar.cast .Usize 1#u32 = 1#usize := by scalar_tac
  rw [hi,bind_tc_ok,hs,bind_tc_ok]
  simp only [if_pos rfl,hm,hc,lift,bind_tc_ok]
  simp only [if_neg (by decide : 1#usize ≠ 0#usize)]
  rw [hn]
  rfl
#print axioms rejectBody
theorem rejectInner : multiproof.verify_in_place_loop0_loop0_loop0 (it 0#usize) id outidx outval 1#usize nodes 224#usize 0#usize 0#u32 none = ok (224#usize,0#usize,some false,it 1#usize) := by
  exact SDY_Loop.done rejectStep _ _ ((rejectStep_eq (it 0#usize) id 224#usize 0#usize).trans rejectBody)
#print axioms rejectInner
theorem rejectParent : multiproof.verify_in_place_loop0_loop0.body hash () 1#usize nodes .Eight outidx outval 224#usize 0#usize 0#usize none = ok (ControlFlow.done (multiproof.Arity.Eight,outidx,outval,1#usize,224#usize,some false,0#u32)) := by
  unfold multiproof.verify_in_place_loop0_loop0.body
  change (do let (a,i,p,b) ← multiproof.verify_in_place_loop0_loop0_loop0 (it 0#usize) id outidx outval 1#usize nodes 224#usize 0#usize 0#u32 none
             match p with
             | none => do
               let d ← aspis_core.r0.merkle.parent_with_digest hash () (Array.from_slice children b.iter.slice)
               let idx1 ← Array.update outidx 0#usize 0#u32
               let val1 ← Array.update outval 0#usize d
               let w ← 0#usize + 1#usize
               ok (ControlFlow.cont (multiproof.Arity.Eight,idx1,val1,a,w,i,none))
             | some _ => ok (ControlFlow.done (multiproof.Arity.Eight,outidx,outval,1#usize,a,p,0#u32))) = _
  rw [rejectInner];rfl
#print axioms rejectParent
theorem rejectLevel : multiproof.verify_in_place_loop0_loop0 hash () .Eight outidx outval 1#usize nodes 224#usize 0#usize 0#usize none = ok (multiproof.Arity.Eight,outidx,outval,1#usize,224#usize,some false,0#u32) := by
  exact SDY_Loop.done pstep _ _ ((pstep_eq .Eight outidx outval 224#usize 0#usize 0#usize none).trans rejectParent)
#print axioms rejectLevel
abbrev OState := core.ops.range.Range U32 × multiproof.Arity × Array U32 16#usize × Array Node 16#usize × Usize × Usize × Option Bool
def ostep (s : OState) := multiproof.verify_in_place_loop0.body hash () (node 0#u8) nodes s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.2.2.2.2.2
theorem range_next (i j : U32) (lt : i.val < 6) (inc : j.val = i.val+1) :
    core.iter.range.IteratorRange.next core.iter.range.StepU32 {start:=i,«end»:=6#u32} = ok (some i,{start:=j,«end»:=6#u32}) := by
  obtain ⟨v,hv,he⟩ := WP.spec_imp_exists (core.iter.range.IteratorRange.next_U32_some_spec {start:=i,«end»:=6#u32} lt)
  rcases v with ⟨o,r⟩
  rcases he with ⟨ho,hr,hend⟩
  have hs : r.start = j := UScalar.eq_imp r.start j (by change r.start.val = i.val+1 at hr; omega)
  have rr : r = {start:=j,«end»:=6#u32} := by cases r; simp_all
  simpa only [ho,rr] using hv
#print axioms range_next
theorem outerFirst : ostep ({start:=0#u32,«end»:=6#u32},.Eight,idx,val,1#usize,0#usize,none) = ok (ControlFlow.cont ({start:=1#u32,«end»:=6#u32},.Eight,outidx,outval,1#usize,224#usize,none)) := by
  unfold ostep multiproof.verify_in_place_loop0.body
  rw [range_next 0#u32 1#u32 (by decide) rfl,bind_tc_ok]
  change (do let (a,x,v,n,offset,p,i) ← multiproof.verify_in_place_loop0_loop0 hash () .Eight idx val 1#usize nodes 0#usize 0#usize 0#usize none
             match i with
             | 1#uscalar => ok (ControlFlow.cont (({start:=1#u32,«end»:=6#u32} : core.ops.range.Range U32),a,x,v,n,offset,p))
             | _ => match p with
               | none => ok (ControlFlow.done (x,v,none))
               | some _ => ok (ControlFlow.done (x,v,p))) = _
  rw [prun];rfl
#print axioms outerFirst
theorem outerLast : ostep ({start:=1#u32,«end»:=6#u32},.Eight,outidx,outval,1#usize,224#usize,none) = ok (ControlFlow.done (outidx,outval,some false)) := by
  unfold ostep multiproof.verify_in_place_loop0.body
  rw [range_next 1#u32 2#u32 (by decide) rfl,bind_tc_ok]
  change (do let (a,x,v,n,offset,p,i) ← multiproof.verify_in_place_loop0_loop0 hash () .Eight outidx outval 1#usize nodes 224#usize 0#usize 0#usize none
             match i with
             | 1#uscalar => ok (ControlFlow.cont (({start:=2#u32,«end»:=6#u32} : core.ops.range.Range U32),a,x,v,n,offset,p))
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
def singleton : Slice U32 := ⟨[10#u32],by scalar_tac⟩
abbrev Pred := multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool
abbrev PredCall := multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut
abbrev ReadIter := core.slice.iter.Iter U32
abbrev AllState := ReadIter × Unit
abbrev AllOut := Bool × ReadIter × Unit
def allBody : AllState → Result (ControlFlow AllState AllOut) :=
  fun (self',predicate') => do
    let (item,self'') ← (core.iter.traits.iterator.IteratorSliceIter U32).next self'
    match item with
    | none => ok (ControlFlow.done (true,self'',predicate'))
    | some value =>
      let (holds,predicate'') ← Pred.call_mut predicate' value
      if holds then ok (ControlFlow.cont (self'',predicate'')) else ok (ControlFlow.done (false,self'',predicate''))
theorem pred_result : PredCall () 10#u32 = ok (true,()) := by
  unfold PredCall multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut multiproof.LEAF_BITS
  rfl
#print axioms pred_result
theorem all_first : allBody (⟨singleton,0⟩,()) = ok (ControlFlow.cont (⟨singleton,1⟩,())) := by
  unfold allBody
  change (do let (b,p) ← PredCall () 10#u32; if b then ok (ControlFlow.cont ((⟨singleton,1⟩ : ReadIter),p)) else ok (ControlFlow.done (false,(⟨singleton,1⟩ : ReadIter),p))) = _
  rw [pred_result]
  rfl
#print axioms all_first
theorem all_last : allBody (⟨singleton,1⟩,()) = ok (ControlFlow.done (true,⟨singleton,1⟩,())) := by rfl
#print axioms all_last
theorem all_run_last : loop allBody (⟨singleton,1⟩,()) = ok (true,⟨singleton,1⟩,()) := SDY_Loop.done allBody _ _ all_last
#print axioms all_run_last
theorem all_run : loop allBody (⟨singleton,0⟩,()) = ok (true,⟨singleton,1⟩,()) := SDY_Loop.next allBody _ _ _ all_first all_run_last
#print axioms all_run
theorem all_result : core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all Pred ⟨singleton,0⟩ () = ok (true,⟨singleton,1⟩) := by
  have hh := congrArg (fun r : Result AllOut => do let out ← r; ok (out.1,out.2.1)) all_run
  unfold core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all core.iter.traits.iterator.Iterator.all.default
  convert hh using 1 <;> try rfl
  congr 2
  funext x
  rcases x with ⟨iter,pred⟩
  cases pred
  unfold allBody
  simp
  all_goals
    intro a b h
    cases a <;> simp
    all_goals
      intros
      split <;> rfl
#print axioms all_result
abbrev WinPred := multiproof.well_formed.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU32Bool
def windows : core.slice.iter.Windows U32 := ⟨singleton,2#usize,0⟩
theorem windows_result : core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.all WinPred windows () = ok (true,windows) := by
  unfold core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.all core.iter.traits.iterator.Iterator.all.default
  rw [loop.eq_def]
  rfl
#print axioms windows_result
theorem formed : multiproof.well_formed singleton = ok true := by
  unfold multiproof.well_formed multiproof.MAX_BATCH
  change (do let (b,_) ← core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.all WinPred windows ()
             if b then do
               let (b2,_) ← core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all Pred ⟨singleton,0⟩ ()
               ok b2
             else ok false) = _
  rw [windows_result,bind_tc_ok]
  simp only [ite_true]
  rw [all_result]
  rfl
#print axioms formed

theorem emitted : multiproof.verify_in_place hash () .Eight (node 0#u8) idx val 1#usize nodes = ok (false,outidx,outval) := by
  have hg : Slice.len nodes = 224#usize := by
    apply UScalar.eq_of_val_eq
    change (List.replicate 224 _).length = 224
    exact List.length_replicate
  have hm : 224#usize % 32#usize = ok 0#usize := by rfl
  have hl : multiproof.Arity.levels .Eight = ok 6#u32 := by
    unfold multiproof.Arity.levels multiproof.Arity.bits multiproof.LEAF_BITS
    rfl
  have hx : core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32)) idx {«end»:=1#usize} = ok singleton := by rfl
  unfold multiproof.verify_in_place
  simp only [multiproof.MAX_BATCH]
  simp only [show (1#usize = 0#usize) = False from propext (by decide),show (1#usize > 16#usize) = False from propext (by decide),ite_false]
  rw [hx,bind_tc_ok,formed,bind_tc_ok]
  simp only [ite_true]
  rw [hg,hm,bind_tc_ok]
  simp only [show (0#usize != 0#usize) = false from rfl, Bool.false_eq_true,ite_false]
  rw [hl,bind_tc_ok,orun]
  rfl
#print axioms emitted
end SDY_MpC
