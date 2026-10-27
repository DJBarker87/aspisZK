from pathlib import Path
E=Path(__file__).resolve().parent
arr=lambda xs,t:'⟨['+','.join(str(x)+'#'+t for x in xs)+'],by simp⟩'
for tag,xs,add in [('A',[0]*8,1),('B',[2147483646]*8,1),('C',[5]*8,2147483647)]:
 ds=[];carry=[add]
 for x in xs:ds.append((x+carry[-1])%2147483647);carry.append((x+carry[-1])//2147483647)
 t=f'''import SDY_Join_Funs
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace SDY_Add{tag}
open SDY_Join_Release
abbrev Iter := core.slice.iter.IterMut U32
abbrev Back := Iter → Iter
abbrev State := Iter × Back × U32
abbrev body := sampler.add_small_base_p_loop.body
def step (s : State) := body s.1 s.2.1 s.2.2
def input : Array U32 8#usize := {arr(xs,'u32')}
def output : Array U32 8#usize := {arr(ds,'u32')}
def it (i : Nat) : Iter := ⟨input.to_slice,i⟩
def restore (i : Nat) (x : U32) : Back := fun r => {{r with slice := r.slice.setAtNat i x}}
def fin8 (b : Back) : Back := b
'''
 for i in reversed(range(8)):t+=f'def fin{i} (b : Back) : Back := fin{i+1} (fun r => b (restore {i} {ds[i]}#u32 r))\n'
 for i in range(9):
  rhs='ok (.done ('+str(carry[i])+'#u32,b))' if i==8 else f'ok (.cont (it {i+1},fun r => b (restore {i} {ds[i]}#u32 r),{carry[i+1]}#u32))'
  t+=f'''\ntheorem step{i} (b : Back) : body (it {i}) b {carry[i]}#u32 = {rhs} := by
  unfold body sampler.add_small_base_p_loop.body
  simp [core.slice.iter.IteratorIterMut.next,it,input,restore,aspis_core.field.P]
  {'skip' if i==8 else 'rfl'}
#print axioms step{i}
'''
 for i in reversed(range(9)):
  t+=f'''\ntheorem run{i} (b : Back) : loop step (it {i},b,{carry[i]}#u32) = ok ({carry[-1]}#u32,fin{i} b) := by
  rw [loop.eq_def]
  change (match body (it {i}) b {carry[i]}#u32 with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step{i}]
  {'rfl' if i==8 else 'exact run'+str(i+1)+' _'}
#print axioms run{i}
'''
 t+=f'''\ntheorem emitted : sampler.add_small_base_p input {add}#u32 = ok ({'true' if carry[-1] else 'false'},output) := by
  unfold sampler.add_small_base_p SDY_Join_intoIter
  simp only [bind_tc_ok]
  change (do let (c,b) ← loop step (it 0,id,{add}#u32); ok (c != 0#u32,Array.from_slice input (b (it 0)).slice)) = _
  rw [run0]
  rfl
#print axioms emitted
end SDY_Add{tag}
'''
 (E/f'SDY_Add{tag}.lean').write_text(t)
for tag,xs,ps,basis,flush in [('A',[1,2,3,4],[1,2,3,4],2,False),('B',[2147483648,2147483649,4294967296,7],[0]*4,0,True),('C',[2147483647,0,0,0],[1,2,3,4],1,True)]:
 ys=[x+p*basis for x,p in zip(xs,ps)];zs=[(x&2147483647)+(x>>31) for x in ys] if flush else ys
 t=f'''import SDY_Join_Funs
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace SDY_Row{tag}
open SDY_Join_Release
abbrev RState := core.ops.range.Range Usize × Array U64 4#usize × aspis_core.field.M31
abbrev rb := verifier.update_residue_row_loop0.body
def rs (s : RState) := rb limbs s.1 s.2.1 s.2.2
'''.replace('def rs (s : RState) := rb limbs s.1 s.2.1 s.2.2\n','')
 t+=f'def limbs : Array U32 4#usize := {arr(ps,"u32")}\ndef rs (s : RState) := rb limbs s.1 s.2.1 s.2.2\n'
 for i in range(5):t+=f'def row{i} : Array U64 4#usize := {arr(ys[:i]+xs[i:],"u64")}\n'
 t+=f'''def power : aspis_core.field.QM31 := ⟨⟨{ps[0]}#u32,{ps[1]}#u32⟩,⟨{ps[2]}#u32,{ps[3]}#u32⟩⟩
def output : Array U64 4#usize := {arr(zs,'u64')}
'''
 for i in range(5):
  lhs=f'rb limbs {{start:={i}#usize,«end»:=4#usize}} row{i} {basis}#u32'
  rhs='ok (.done row4)' if i==4 else f'ok (.cont ({{start:={i+1}#usize,«end»:=4#usize}},row{i+1},{basis}#u32))'
  t+=f'theorem rstep{i} : {lhs} = {rhs} := by rfl\n#print axioms rstep{i}\n'
 for i in reversed(range(5)):
  t+=f'''theorem rrun{i} : loop rs ({{start:={i}#usize,«end»:=4#usize}},row{i},{basis}#u32) = ok row4 := by
  rw [loop.eq_def]
  change (match rb limbs {{start:={i}#usize,«end»:=4#usize}} row{i} {basis}#u32 with
    | ok (.cont s) => loop rs s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [rstep{i}]
  {'rfl' if i==4 else 'exact rrun'+str(i+1)}
#print axioms rrun{i}
'''
 if flush:
  t+='''abbrev Iter := core.slice.iter.IterMut U64
abbrev Back := Iter → Iter
abbrev State := Iter × Back
abbrev body := verifier.update_residue_row_loop1.body
def step (s : State) := body s.1 s.2
def it (i : Nat) : Iter := ⟨row4.to_slice,i⟩
def restore (i : Nat) (x : U64) : Back := fun r => {r with slice := r.slice.setAtNat i x}
def fin4 (b : Back) : Back := b
'''
  for i in reversed(range(4)):t+=f'def fin{i} (b : Back) : Back := fin{i+1} (fun r => b (restore {i} {zs[i]}#u64 r))\n'
  for i in range(5):
   rhs='ok (.done b)' if i==4 else f'ok (.cont (it {i+1},fun r => b (restore {i} {zs[i]}#u64 r)))'
   t+=f'''theorem step{i} (b : Back) : body (it {i}) b = {rhs} := by
  unfold body verifier.update_residue_row_loop1.body
  simp [core.slice.iter.IteratorIterMut.next,it,row4,restore]
  {'skip' if i==4 else 'rfl'}
#print axioms step{i}
'''
  for i in reversed(range(5)):
   t+=f'''theorem run{i} (b : Back) : loop step (it {i},b) = ok (fin{i} b) := by
  rw [loop.eq_def]
  change (match body (it {i}) b with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step{i}]
  {'rfl' if i==4 else 'exact run'+str(i+1)+' _'}
#print axioms run{i}
'''
 t+=f'''theorem emitted : verifier.update_residue_row row0 power {basis}#u32 {'true' if flush else 'false'} = ok output := by
  unfold verifier.update_residue_row
  change (do let row ← loop rs ({{start:=0#usize,«end»:=4#usize}},row0,{basis}#u32); {('let (iter,back) ← SDY_Join_intoIter row; let b ← verifier.update_residue_row_loop1 iter id; ok (back b)' if flush else 'ok row')}) = _
  rw [rrun0]
'''
 if flush:
  t+=f'''  simp only [bind_tc_ok]
  unfold SDY_Join_intoIter
  simp only [bind_tc_ok]
  change (do let b ← loop step (it 0,id); ok (Array.from_slice row4 (b (it 0)).slice)) = _
  rw [run0]
  rfl
'''
 else:t+='  rfl\n'
 t+=f'#print axioms emitted\nend SDY_Row{tag}\n'
 (E/f'SDY_Row{tag}.lean').write_text(t)
for tag,raw,zs in [('A',[1,2,3,4],[1,2,3,4]),('B',[2147483648,2147483649,4294967296,7],[1,2,2,7]),('C',[2147483647,4294967294,0,2147483652],[0,0,0,5])]:
 t=f'''import SDY_Join_Funs
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace SDY_Finish{tag}
open SDY_Join_Release
abbrev Q := aspis_core.field.QM31
abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut Q)
abbrev Back := Iter → Iter
abbrev State := Iter × Back
abbrev body := verifier.BatchedWeights.finish_loop.body
def step (s : State) := body state s.1 s.2
'''.replace('def step (s : State) := body state s.1 s.2\n','')
 t+=f'''def old : Q := ⟨⟨99#u32,99#u32⟩,⟨99#u32,99#u32⟩⟩
def value : Q := ⟨⟨{zs[0]}#u32,{zs[1]}#u32⟩,⟨{zs[2]}#u32,{zs[3]}#u32⟩⟩
def input : Slice Q := ⟨[old],by simp⟩
def output : Slice Q := ⟨[value],by simp⟩
def state : verifier.BatchedWeights := ⟨⟨[{arr(raw,'u64')}],by simp⟩,0#usize⟩
def step (s : State) := body state s.1 s.2
def it (i : Nat) : Iter := ⟨⟨input,i⟩,if i=0 then 0#usize else 1#usize⟩
def restore : Back := fun r => {{r with iter := {{r.iter with slice := r.iter.slice.setAtNat 0 value}}}}
theorem value_result : verifier.BatchedWeights.value state 0#usize = ok value := by rfl
#print axioms value_result

theorem first (b : Back) : body state (it 0) b = ok (.cont (it 1,fun r => b (restore r))) := by
  unfold body verifier.BatchedWeights.finish_loop.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,input]
  rw [value_result]
  rfl
#print axioms first

theorem last (b : Back) : body state (it 1) b = ok (.done b) := by
  unfold body verifier.BatchedWeights.finish_loop.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,input]
#print axioms last

theorem run1 (b : Back) : loop step (it 1,b) = ok b := by
  rw [loop.eq_def]
  change (match body state (it 1) b with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [last]
  rfl
#print axioms run1

theorem run0 (b : Back) : loop step (it 0,b) = ok (fun r => b (restore r)) := by
  rw [loop.eq_def]
  change (match body state (it 0) b with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [first]
  exact run1 _
#print axioms run0

theorem emitted : verifier.BatchedWeights.finish state input = ok output := by
  unfold verifier.BatchedWeights.finish core.slice.Slice.iter_mut SDY_Join_enumerateRestored core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.enumerate
  simp only [bind_tc_ok]
  change (do let b ← loop step (it 0,id); ok (b (it 0)).iter.slice) = _
  rw [run0]
  rfl
#print axioms emitted
end SDY_Finish{tag}
'''
 (E/f'SDY_Finish{tag}.lean').write_text(t)
