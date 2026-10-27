from pathlib import Path
E=Path(__file__).resolve().parent
for tag,index,leaf,sib,digest in [('A',8,5,2,5),('B',9,7,3,3),('C',10,9,4,4)]:
 t=f'''import SDY_Join_Funs
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace SDY_Mp{tag}
open SDY_Join_Release
abbrev Node := Array U8 32#usize
def node (x : U8) : Node := Array.repeat 32#usize x
def hash : aspis_core.digest.Digest32 Unit := {{digest := fun _ parts => ok (node ((parts.val[1]?.map (fun s => s.val[0]?.getD 0#u8)).getD 0#u8))}}
def idx : Array U32 16#usize := ⟨{index}#u32 :: List.replicate 15 0#u32,by simp⟩
def val : Array Node 16#usize := ⟨node {leaf}#u8 :: List.replicate 15 (node 0#u8),by simp⟩
def outidx : Array U32 16#usize := ⟨1#u32 :: List.replicate 15 0#u32,by simp⟩
def outval : Array Node 16#usize := ⟨node {digest}#u8 :: List.replicate 15 (node 0#u8),by simp⟩
def nodes : Slice U8 := ⟨List.replicate 224 {sib}#u8,by simp⟩
abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut Node)
abbrev Back := Iter → Iter
abbrev State := Iter × Back × Usize × Usize
abbrev body := multiproof.verify_in_place_loop0_loop0_loop0.body
'''
 # children slice initially all zero, source iterator reads original children, writes deferred.
 t+='''def children : Array Node 8#usize := Array.repeat 8#usize (node 0#u8)
def it (j : Nat) : Iter := ⟨⟨children.to_slice,j⟩,UScalar.ofNat j (by omega)⟩
'''.replace('def it (j : Nat) : Iter := ⟨⟨children.to_slice,j⟩,UScalar.ofNat j (by omega)⟩','def it (j : Usize) : Iter := ⟨⟨children.to_slice,j.val⟩,j⟩')
 t+='''def restore (j : Nat) (v : Node) : Back := fun r => {r with iter := {r.iter with slice := r.iter.slice.setAtNat j v}}
def step (s : State) := body idx val 1#usize nodes 1#u32 none s.1 s.2.1 s.2.2.1 s.2.2.2
'''
 at=0;i=0;ats=[0];iss=[0];cs=[]
 for j in range(8):
  if j==index%8:cs.append(leaf);i=1
  else:cs.append(sib);at+=32
  ats.append(at);iss.append(i)
 t+='def fin8 (b : Back) : Back := b\n'
 for j in reversed(range(8)):t+=f'def fin{j} (b : Back) : Back := fin{j+1} (fun r => b (restore {j} (node {cs[j]}#u8) r))\n'
 for j in range(9):
  rhs=f'ok (.done ({ats[j]}#usize,{iss[j]}#usize,none,b (it 8#usize)))' if j==8 else f'ok (.cont (it {j+1}#usize,fun r => b (restore {j} (node {cs[j]}#u8) r),{ats[j+1]}#usize,{iss[j+1]}#usize))'
  t+=f'''theorem step{j} (b : Back) : body idx val 1#usize nodes 1#u32 none (it {j}#usize) b {ats[j]}#usize {iss[j]}#usize = {rhs} := by
  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  {'skip' if j==8 else 'rfl'}
#print axioms step{j}
'''
 for j in reversed(range(9)):
  t+=f'''theorem run{j} (b : Back) : loop step (it {j}#usize,b,{ats[j]}#usize,{iss[j]}#usize) = ok (224#usize,1#usize,none,fin{j} b (it 8#usize)) := by
  rw [loop.eq_def]
  change (match body idx val 1#usize nodes 1#u32 none (it {j}#usize) b {ats[j]}#usize {iss[j]}#usize with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step{j}]
  {'rfl' if j==8 else 'exact run'+str(j+1)+' _'}
#print axioms run{j}
'''
 t+='''theorem inner : multiproof.verify_in_place_loop0_loop0_loop0 (it 0#usize) id idx val 1#usize nodes 0#usize 0#usize 1#u32 none = ok (224#usize,1#usize,none,fin0 id (it 8#usize)) := run0 id
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
'''
 # next inner outer terminal .i1==n1 no body computation after parent
 t+='''abbrev PState := multiproof.Arity × Array U32 16#usize × Array Node 16#usize × Usize × Usize × Usize × Option Bool
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
'''
 (E/f'SDY_Mp{tag}.lean').write_text(t)
 t+='''
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
'''
 t+=f'''def singleton : Slice U32 := ⟨[{index}#u32],by simp⟩
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
               let (x,v,p) ← multiproof.verify_in_place_loop0 hash {{start:=0#u32,«end»:=6#u32}} () .Eight (node 0#u8) idx val 1#usize nodes 0#usize none
               match p with
               | none => fail .panic
               | some b => ok (b,x,v)
             else ok (false,idx,val)) = _
  rw [formed]
  simp only [bind_tc_ok,ite_true]
  rw [orun]
  rfl
#print axioms emitted
end SDY_Mp{tag}
'''
 (E/f'SDY_Mp{tag}.lean').write_text(t)
