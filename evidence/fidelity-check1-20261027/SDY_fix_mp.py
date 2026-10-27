from pathlib import Path
import re
E=Path(__file__).resolve().parent
# Apply to the original fixture drafts; do not run after further manual changes.
for tag,index in [('A',8),('B',9),('C',10)]:
 p=E/f'SDY_Mp{tag}.lean';s=p.read_text()
 s=s.replace('def hash :','def copyUnit : core.marker.Copy Unit := ⟨⟨fun x => ok x⟩⟩\ndef hash :').replace(':= {digest :=',':= {coremarkerCopyInst := copyUnit,digest :=')
 s=s.replace('List.replicate 224 '+str({'A':2,'B':3,'C':4}[tag])+'#u8,by simp','List.replicate 224 '+str({'A':2,'B':3,'C':4}[tag])+'#u8,by simp only [List.length_replicate]; scalar_tac')
 s=s.replace('def singleton : Slice U32 := ⟨['+str(index)+'#u32],by simp⟩','def singleton : Slice U32 := ⟨['+str(index)+'#u32],by scalar_tac⟩')
 s=re.sub(r'\bat\b','offset',s)
 ats=[0];iss=[0];offset=0;ii=0
 for j in range(8):
  if j==index%8:ii=1
  else:offset+=32
  ats.append(offset);iss.append(ii)
 # Each concrete body's two checked usize additions get named arithmetic facts.
 for j in range(8):
  start=s.index(' := by',s.index(f'theorem step{j}'))+len(' := by');end=s.index(f'\n#print axioms step{j}',start)
  extra=f'  rw [add_eq {j}#usize 1#usize {j+1}#usize rfl]\n'
  if j==index%8:extra+=f'  rw [add_eq {iss[j]}#usize 1#usize {iss[j+1]}#usize rfl]\n'
  else:extra+=f'  rw [add_eq {ats[j]}#usize 32#usize {ats[j+1]}#usize rfl]\n'
  s=s[:end-len('\n  rfl')]+ '\n'+extra+'  rfl'+s[end:] if s[end-len('\n  rfl'):end]=='\n  rfl' else s
 # Symbolic uncurry equalities, avoiding concrete whole-body conversion.
 marker='theorem step0'
 pos=s.index(marker);s=s[:pos]+'''theorem step_eq (iter : Iter) (b : Back) (offset i : Usize) :
    step (iter,b,offset,i) = body idx val 1#usize nodes 1#u32 none iter b offset i := rfl
#print axioms step_eq
'''+s[pos:]
 for j in range(9):
  start=s.index(' := by',s.index(f'theorem run{j}'))+len(' := by');end=s.index(f'\n#print axioms run{j}',start)
  h=f'((step_eq (it {j}#usize) b {ats[j]}#usize {iss[j]}#usize).trans (step{j} b))'
  rhs=f'\n  exact SDY_Loop.done step _ _ {h}' if j==8 else f'\n  exact SDY_Loop.next step _ _ _ {h} (run{j+1} _)'
  s=s[:start]+rhs+s[end:]
 # Remove post-rw tactics that are already closed by reflexive simplification.
 s=s.replace('rw [loop.eq_def,pend];rfl','exact SDY_Loop.done pstep _ _ pend')
 # Prun starts with a known body result, match through symbolic pstep equality.
 pos=s.index('theorem pend');s=s[:pos]+'''theorem pstep_eq (a : multiproof.Arity) (x : Array U32 16#usize) (v : Array Node 16#usize) (offset w i : Usize) (p : Option Bool) :
    pstep (a,x,v,offset,w,i,p) = multiproof.verify_in_place_loop0_loop0.body hash () 1#usize nodes a x v offset w i p := rfl
#print axioms pstep_eq
'''+s[pos:]
 start=s.index(' := by',s.index('theorem prun :'))+len(' := by');end=s.index('\n#print axioms prun',start)
 s=s[:start]+'''\n  exact SDY_Loop.next pstep _ _ _ ((pstep_eq .Eight idx val 0#usize 0#usize 0#usize none).trans parent) prunEnd'''+s[end:]
 # Restore rejection step as a separately evaluated body.
 start=s.index(' := by',s.index('theorem rejectBody'))+len(' := by');end=s.index('\n#print axioms rejectBody',start)
 s=s[:start]+'''\n  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  rw [add_eq 0#usize 1#usize 1#usize rfl,add_eq 224#usize 32#usize 256#usize rfl]
  rfl'''+s[end:]
 pos=s.index('theorem rejectBody');s=s[:pos]+'''theorem rejectStep_eq (iter : Iter) (b : Back) (offset i : Usize) :
    rejectStep (iter,b,offset,i) = body outidx outval 1#usize nodes 0#u32 none iter b offset i := rfl
#print axioms rejectStep_eq
'''+s[pos:]
 start=s.index(' := by',s.index('theorem rejectInner'))+len(' := by');end=s.index('\n#print axioms rejectInner',start)
 s=s[:start]+'''\n  exact SDY_Loop.done rejectStep _ _ ((rejectStep_eq (it 0#usize) id 224#usize 0#usize).trans rejectBody)'''+s[end:]
 start=s.index(' := by',s.index('theorem rejectLevel'))+len(' := by');end=s.index('\n#print axioms rejectLevel',start)
 s=s[:start]+'''\n  exact SDY_Loop.done pstep _ _ ((pstep_eq .Eight outidx outval 224#usize 0#usize 0#usize none).trans rejectParent)'''+s[end:]
 s=s.replace('rw [loop.eq_def,outerLast];rfl','exact SDY_Loop.done ostep _ _ outerLast')
 start=s.index(' := by',s.index('theorem orun :'))+len(' := by');end=s.index('\n#print axioms orun',start)
 s=s[:start]+'''\n  exact SDY_Loop.next ostep _ _ _ outerFirst orunLast'''+s[end:]
 # Let the guards' irreducible constants unfold before the source-level change.
 s=s.replace('  unfold multiproof.verify_in_place\n','  unfold multiproof.verify_in_place\n  simp only [multiproof.MAX_BATCH]\n')
 p.write_text(s)
