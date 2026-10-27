from pathlib import Path
import re
E=Path(__file__).resolve().parent
for tag,index,x in [('A',8,2),('B',9,3),('C',10,4)]:
 p=E/f'SDY_Mp{tag}.lean';s=p.read_text().replace('import SDY_Loop','import SDY_Slice')
 s=s.replace('def copyUnit : core.marker.Copy Unit := ⟨⟨fun x => ok x⟩⟩','def copyUnit : core.marker.Copy Unit := {cloneInst := {clone := fun x => ok x}}')
 s=re.sub(r'def nodes : Slice U8 :=[^\n]+',f'def nodes : Slice U8 := SDY_Slice.nodes {x}#u8',s)
 ats=[0];iss=[0];offset=0;ii=0
 for j in range(8):
  if j==index%8:ii=1
  else:offset+=32
  ats.append(offset);iss.append(ii)
 for j in range(8):
  start=s.index(' := by',s.index(f'theorem step{j}'))+len(' := by');end=s.index(f'\n#print axioms step{j}',start)
  proof='''\n  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
'''
  proof+=f'  rw [add_eq {j}#usize 1#usize {j+1}#usize rfl]\n'
  if j==index%8:
   if iss[j]!=j:proof+=f'  rw [add_eq {iss[j]}#usize 1#usize {iss[j+1]}#usize rfl]\n'
  else:
   proof+=f'  rw [add_eq {ats[j]}#usize 32#usize {ats[j+1]}#usize rfl]\n  simp only [bind_tc_ok]\n  unfold nodes\n  rw [SDY_Slice.read {x}#u8 {ats[j]}#usize {ats[j+1]}#usize (by decide) (by decide) rfl]\n'
  proof+='  rfl'
  s=s[:start]+proof+s[end:]
 # Reject input node range: prove none before reducing list contents.
 start=s.index(' := by',s.index('theorem rejectBody'))+len(' := by');end=s.index('\n#print axioms rejectBody',start)
 s=s[:start]+'''\n  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  rw [add_eq 0#usize 1#usize 1#usize rfl,add_eq 224#usize 32#usize 256#usize rfl]
  simp only [bind_tc_ok]
  have hn : core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8) nodes {start:=224#usize,«end»:=256#usize} = ok none := by
    simp [core.slice.Slice.get,core.slice.index.SliceIndexRangeUsizeSlice,core.slice.index.SliceIndexRangeUsizeSlice.get,nodes,SDY_Slice.nodes,Slice.length]
  simp [multiproof.index_at,outidx]
  rw [hn]
  rfl'''+s[end:]
 # In the explicitly typed outer-body expressions Lean can infer ControlFlow.
 for name in ['outerFirst','outerLast']:
  start=s.index(' := by',s.index('theorem '+name))+len(' := by');end=s.index('\n#print axioms '+name,start)
  proof=s[start:end]
  proof=proof.replace('ok (.cont','ok (ControlFlow.cont').replace('ok (.done','ok (ControlFlow.done')
  s=s[:start]+proof+s[end:]
 # Unfold the immutable singleton iterator before rewriting its loop.
 s=s.replace('  unfold core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all core.iter.traits.iterator.Iterator.all.default','  unfold core.slice.Slice.iter\n  simp only [bind_tc_ok]\n  unfold core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all core.iter.traits.iterator.Iterator.all.default')
 p.write_text(s)
