import SDY_Join_Funs
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace SDY_MpB
open SDY_Join_Release
abbrev Node := Array U8 32#usize
def node (x : U8) : Node := Array.repeat 32#usize x
def hash : aspis_core.digest.Digest32 Unit := {digest := fun _ parts => ok (node ((parts.val[1]?.map (fun s => s.val[0]?.getD 0#u8)).getD 0#u8))}
def idx : Array U32 16#usize := ⟨9#u32 :: List.replicate 15 0#u32,by simp⟩
def val : Array Node 16#usize := ⟨node 7#u8 :: List.replicate 15 (node 0#u8),by simp⟩
def outidx : Array U32 16#usize := ⟨1#u32 :: List.replicate 15 0#u32,by simp⟩
def outval : Array Node 16#usize := ⟨node 3#u8 :: List.replicate 15 (node 0#u8),by simp⟩
def nodes : Slice U8 := ⟨List.replicate 224 3#u8,by simp⟩
abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut Node)
abbrev Back := Iter → Iter
abbrev State := Iter × Back × Usize × Usize
abbrev body := multiproof.verify_in_place_loop0_loop0_loop0.body
def children : Array Node 8#usize := Array.repeat 8#usize (node 0#u8)
def it (j : Usize) : Iter := ⟨⟨children.to_slice,j.val⟩,j⟩
def restore (j : Nat) (v : Node) : Back := fun r => {r with iter := {r.iter with slice := r.iter.slice.setAtNat j v}}
def step (s : State) := body idx val 1#usize nodes 1#u32 none s.1 s.2.1 s.2.2.1 s.2.2.2
def fin8 (b : Back) : Back := b
def fin7 (b : Back) : Back := fin8 (fun r => b (restore 7 (node 3#u8) r))
def fin6 (b : Back) : Back := fin7 (fun r => b (restore 6 (node 3#u8) r))
def fin5 (b : Back) : Back := fin6 (fun r => b (restore 5 (node 3#u8) r))
def fin4 (b : Back) : Back := fin5 (fun r => b (restore 4 (node 3#u8) r))
def fin3 (b : Back) : Back := fin4 (fun r => b (restore 3 (node 3#u8) r))
def fin2 (b : Back) : Back := fin3 (fun r => b (restore 2 (node 3#u8) r))
def fin1 (b : Back) : Back := fin2 (fun r => b (restore 1 (node 7#u8) r))
def fin0 (b : Back) : Back := fin1 (fun r => b (restore 0 (node 3#u8) r))
theorem step0 (b : Back) : body idx val 1#usize nodes 1#u32 none (it 0#usize) b 0#usize 0#usize = ok (.cont (it 1#usize,fun r => b (restore 0 (node 3#u8) r),32#usize,0#usize)) := by
  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  rfl
#print axioms step0
theorem step1 (b : Back) : body idx val 1#usize nodes 1#u32 none (it 1#usize) b 32#usize 0#usize = ok (.cont (it 2#usize,fun r => b (restore 1 (node 7#u8) r),32#usize,1#usize)) := by
  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  rfl
#print axioms step1
theorem step2 (b : Back) : body idx val 1#usize nodes 1#u32 none (it 2#usize) b 32#usize 1#usize = ok (.cont (it 3#usize,fun r => b (restore 2 (node 3#u8) r),64#usize,1#usize)) := by
  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  rfl
#print axioms step2
theorem step3 (b : Back) : body idx val 1#usize nodes 1#u32 none (it 3#usize) b 64#usize 1#usize = ok (.cont (it 4#usize,fun r => b (restore 3 (node 3#u8) r),96#usize,1#usize)) := by
  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  rfl
#print axioms step3
theorem step4 (b : Back) : body idx val 1#usize nodes 1#u32 none (it 4#usize) b 96#usize 1#usize = ok (.cont (it 5#usize,fun r => b (restore 4 (node 3#u8) r),128#usize,1#usize)) := by
  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  rfl
#print axioms step4
theorem step5 (b : Back) : body idx val 1#usize nodes 1#u32 none (it 5#usize) b 128#usize 1#usize = ok (.cont (it 6#usize,fun r => b (restore 5 (node 3#u8) r),160#usize,1#usize)) := by
  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  rfl
#print axioms step5
theorem step6 (b : Back) : body idx val 1#usize nodes 1#u32 none (it 6#usize) b 160#usize 1#usize = ok (.cont (it 7#usize,fun r => b (restore 6 (node 3#u8) r),192#usize,1#usize)) := by
  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  rfl
#print axioms step6
theorem step7 (b : Back) : body idx val 1#usize nodes 1#u32 none (it 7#usize) b 192#usize 1#usize = ok (.cont (it 8#usize,fun r => b (restore 7 (node 3#u8) r),224#usize,1#usize)) := by
  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  rfl
#print axioms step7
theorem step8 (b : Back) : body idx val 1#usize nodes 1#u32 none (it 8#usize) b 224#usize 1#usize = ok (.done (224#usize,1#usize,none,b (it 8#usize))) := by
  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  skip
#print axioms step8
theorem run8 (b : Back) : loop step (it 8#usize,b,224#usize,1#usize) = ok (224#usize,1#usize,none,fin8 b (it 8#usize)) := by
  rw [loop.eq_def]
  change (match body idx val 1#usize nodes 1#u32 none (it 8#usize) b 224#usize 1#usize with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step8]
  rfl
#print axioms run8
theorem run7 (b : Back) : loop step (it 7#usize,b,192#usize,1#usize) = ok (224#usize,1#usize,none,fin7 b (it 8#usize)) := by
  rw [loop.eq_def]
  change (match body idx val 1#usize nodes 1#u32 none (it 7#usize) b 192#usize 1#usize with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step7]
  exact run8 _
#print axioms run7
theorem run6 (b : Back) : loop step (it 6#usize,b,160#usize,1#usize) = ok (224#usize,1#usize,none,fin6 b (it 8#usize)) := by
  rw [loop.eq_def]
  change (match body idx val 1#usize nodes 1#u32 none (it 6#usize) b 160#usize 1#usize with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step6]
  exact run7 _
#print axioms run6
theorem run5 (b : Back) : loop step (it 5#usize,b,128#usize,1#usize) = ok (224#usize,1#usize,none,fin5 b (it 8#usize)) := by
  rw [loop.eq_def]
  change (match body idx val 1#usize nodes 1#u32 none (it 5#usize) b 128#usize 1#usize with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step5]
  exact run6 _
#print axioms run5
theorem run4 (b : Back) : loop step (it 4#usize,b,96#usize,1#usize) = ok (224#usize,1#usize,none,fin4 b (it 8#usize)) := by
  rw [loop.eq_def]
  change (match body idx val 1#usize nodes 1#u32 none (it 4#usize) b 96#usize 1#usize with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step4]
  exact run5 _
#print axioms run4
theorem run3 (b : Back) : loop step (it 3#usize,b,64#usize,1#usize) = ok (224#usize,1#usize,none,fin3 b (it 8#usize)) := by
  rw [loop.eq_def]
  change (match body idx val 1#usize nodes 1#u32 none (it 3#usize) b 64#usize 1#usize with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step3]
  exact run4 _
#print axioms run3
theorem run2 (b : Back) : loop step (it 2#usize,b,32#usize,1#usize) = ok (224#usize,1#usize,none,fin2 b (it 8#usize)) := by
  rw [loop.eq_def]
  change (match body idx val 1#usize nodes 1#u32 none (it 2#usize) b 32#usize 1#usize with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step2]
  exact run3 _
#print axioms run2
theorem run1 (b : Back) : loop step (it 1#usize,b,32#usize,0#usize) = ok (224#usize,1#usize,none,fin1 b (it 8#usize)) := by
  rw [loop.eq_def]
  change (match body idx val 1#usize nodes 1#u32 none (it 1#usize) b 32#usize 0#usize with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step1]
  exact run2 _
#print axioms run1
theorem run0 (b : Back) : loop step (it 0#usize,b,0#usize,0#usize) = ok (224#usize,1#usize,none,fin0 b (it 8#usize)) := by
  rw [loop.eq_def]
  change (match body idx val 1#usize nodes 1#u32 none (it 0#usize) b 0#usize 0#usize with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step0]
  exact run1 _
#print axioms run0
theorem inner : multiproof.verify_in_place_loop0_loop0_loop0 (it 0#usize) id idx val 1#usize nodes 0#usize 0#usize 1#u32 none = ok (224#usize,1#usize,none,fin0 id (it 8#usize)) := run0 id
#print axioms inner

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
theorem pend : pstep (.Eight,outidx,outval,224#usize,1#usize,1#usize,none) = ok (.done (.Eight,outidx,outval,1#usize,224#usize,none,1#u32)) := by rfl
#print axioms pend
theorem prunEnd : loop pstep (.Eight,outidx,outval,224#usize,1#usize,1#usize,none) = ok (.Eight,outidx,outval,1#usize,224#usize,none,1#u32) := by
  rw [loop.eq_def,pend];rfl
#print axioms prunEnd
theorem prun : multiproof.verify_in_place_loop0_loop0 hash () .Eight idx val 1#usize nodes 0#usize 0#usize 0#usize none = ok (.Eight,outidx,outval,1#usize,224#usize,none,1#u32) := by
  change loop pstep (.Eight,idx,val,0#usize,0#usize,0#usize,none) = _
  rw [loop.eq_def]
  change (match multiproof.verify_in_place_loop0_loop0.body hash () 1#usize nodes .Eight idx val 0#usize 0#usize 0#usize none with
    | ok (.cont s) => loop pstep s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [parent]
  exact prunEnd
#print axioms prun

def rejectStep (s : State) := body outidx outval 1#usize nodes 0#u32 none s.1 s.2.1 s.2.2.1 s.2.2.2
theorem rejectBody : body outidx outval 1#usize nodes 0#u32 none (it 0#usize) id 224#usize 0#usize = ok (.done (224#usize,0#usize,some false,it 1#usize)) := by rfl
#print axioms rejectBody
theorem rejectInner : multiproof.verify_in_place_loop0_loop0_loop0 (it 0#usize) id outidx outval 1#usize nodes 224#usize 0#usize 0#u32 none = ok (224#usize,0#usize,some false,it 1#usize) := by
  change loop rejectStep (it 0#usize,id,224#usize,0#usize) = _
  rw [loop.eq_def]
  change (match body outidx outval 1#usize nodes 0#u32 none (it 0#usize) id 224#usize 0#usize with
    | ok (.cont s) => loop rejectStep s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [rejectBody];rfl
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
  change loop pstep (.Eight,outidx,outval,224#usize,0#usize,0#usize,none) = _
  rw [loop.eq_def]
  change (match multiproof.verify_in_place_loop0_loop0.body hash () 1#usize nodes .Eight outidx outval 224#usize 0#usize 0#usize none with
    | ok (.cont s) => loop pstep s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [rejectParent];rfl
#print axioms rejectLevel
abbrev OState := core.ops.range.Range U32 × multiproof.Arity × Array U32 16#usize × Array Node 16#usize × Usize × Usize × Option Bool
def ostep (s : OState) := multiproof.verify_in_place_loop0.body hash () (node 0#u8) nodes s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.2.2.2.2.2
theorem outerFirst : ostep ({start:=0#u32,«end»:=6#u32},.Eight,idx,val,1#usize,0#usize,none) = ok (.cont ({start:=1#u32,«end»:=6#u32},.Eight,outidx,outval,1#usize,224#usize,none)) := by
  unfold ostep multiproof.verify_in_place_loop0.body
  change (do let (a,x,v,n,at,p,i) ← multiproof.verify_in_place_loop0_loop0 hash () .Eight idx val 1#usize nodes 0#usize 0#usize 0#usize none
             match i with
             | 1#uscalar => ok (.cont ({start:=1#u32,«end»:=6#u32},a,x,v,n,at,p))
             | _ => match p with
               | none => ok (.done (x,v,none))
               | some _ => ok (.done (x,v,p))) = _
  rw [prun];rfl
#print axioms outerFirst
theorem outerLast : ostep ({start:=1#u32,«end»:=6#u32},.Eight,outidx,outval,1#usize,224#usize,none) = ok (.done (outidx,outval,some false)) := by
  unfold ostep multiproof.verify_in_place_loop0.body
  change (do let (a,x,v,n,at,p,i) ← multiproof.verify_in_place_loop0_loop0 hash () .Eight outidx outval 1#usize nodes 224#usize 0#usize 0#usize none
             match i with
             | 1#uscalar => ok (.cont ({start:=2#u32,«end»:=6#u32},a,x,v,n,at,p))
             | _ => match p with
               | none => ok (.done (x,v,none))
               | some _ => ok (.done (x,v,p))) = _
  rw [rejectLevel];rfl
#print axioms outerLast
theorem orunLast : loop ostep ({start:=1#u32,«end»:=6#u32},.Eight,outidx,outval,1#usize,224#usize,none) = ok (outidx,outval,some false) := by
  rw [loop.eq_def,outerLast];rfl
#print axioms orunLast
theorem orun : multiproof.verify_in_place_loop0 hash {start:=0#u32,«end»:=6#u32} () .Eight (node 0#u8) idx val 1#usize nodes 0#usize none = ok (outidx,outval,some false) := by
  change loop ostep ({start:=0#u32,«end»:=6#u32},.Eight,idx,val,1#usize,0#usize,none) = _
  rw [loop.eq_def,outerFirst]
  exact orunLast
#print axioms orun
def singleton : Slice U32 := ⟨[9#u32],by simp⟩
theorem formed : multiproof.well_formed singleton = ok true := by
  unfold multiproof.well_formed
  simp [singleton,multiproof.MAX_BATCH,core.slice.Slice.is_empty,core.slice.Slice.windows]
  unfold core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.all core.iter.traits.iterator.Iterator.all.default
  rw [loop.eq_def]
  simp [core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next,singleton]
  unfold core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all core.iter.traits.iterator.Iterator.all.default
  rw [loop.eq_def]
  simp [core.slice.iter.IteratorSliceIter.next,singleton,multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut,multiproof.LEAF_BITS]
  rw [loop.eq_def]
  rfl
#print axioms formed

theorem emitted : multiproof.verify_in_place hash () .Eight (node 0#u8) idx val 1#usize nodes = ok (false,outidx,outval) := by
  unfold multiproof.verify_in_place
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
end SDY_MpB
