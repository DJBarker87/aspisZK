from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=(L/'PV_RunJoin_NullifierControl17.lean').read_text();s=s[:s.index('def keyIter0')] if 'def keyIter0' in s else s[:s.index('theorem absorb_key')]
s=s.replace('import R1Z.PV_RunJoin_FixtureArguments','import R1Z.PV_RunJoin_FixtureArguments\nimport R1Z.PV_RunJoin_EnumerateTrace') if 'import R1Z.PV_RunJoin_EnumerateTrace' not in s else s
for name,base,offset in [('key',[0]*8+[1095958530,16]+[0]*6,10),('salt',list(map(int,re.search(r'def s_4_23 .*? := !\[(.*?)\]',(L/'PV_RunJoin_FixtureHashData.lean').read_text())[1].split(','))),100)]:
 for j in range(9):
  it=f'⟨⟨⟨{name}.val,by rw [{name}.property]; scalar_tac⟩,{j}⟩,{j}#usize⟩'
  s+=f'def {name}Iter{j} : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter U32) := {it}\n'
  s+=f'def {name}State{j} : PV_Src_PortSboxStep.State := Array.make 16#usize ['+','.join(f'{v}#u32' for v in base)+']\n'
  if j<8:base[j]=(base[j]+offset+1+17*j)%2147483647
 for j in range(9):
  result=f'(some ({j}#usize,{offset+1+17*j}#u32),{name}Iter{j+1})' if j<8 else f'(none,{name}Iter8)'
  s+=f'''theorem {name}Next{j} : core.iter.adapters.enumerate.IteratorEnumerate.next
    (core.iter.traits.iterator.IteratorSliceIter U32) {name}Iter{j} = ok {result} := by
  unfold core.iter.adapters.enumerate.IteratorEnumerate.next
  change (do
    let (o,it) ← core.slice.iter.IteratorSliceIter.next {name}Iter{j}.iter
    match o with
    | none => ok (none,(⟨it,{j}#usize⟩ : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter U32)))
    | some a => do
      let n ← ({j}#usize) + 1#usize
      ok (some ({j}#usize,a),(⟨it,n⟩ : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter U32)))) = _
  unfold core.slice.iter.IteratorSliceIter.next
  simp only [Slice.len_val]
'''
  if j<8:
   s+=f'''  rw [dif_pos (by change {j} < 8; decide)]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_EnumerateTrace.checked_next _ (by simp)]
  have hn : Usize.wrapping_add {j}#usize 1#usize = {j+1}#usize := by
    apply UScalar.eq_of_val_eq
    rw [uadd _ _ (by simp)]
    rfl
  rw [hn]
  with_unfolding_all rfl
'''
  else:s+='  rw [dif_neg (by change ¬ (8 < 8); decide)]\n  with_unfolding_all rfl\n'
  s+=f'#print axioms {name}Next{j}\n'
 s+=f'theorem absorb_{name} : poseidon2.hash_fields_with_trace_loop0_loop0 {name}Iter '+('initial = ok s4_0' if name=='key' else 's4_23 = ok s5_0')+' := by\n'
 s+=f'  change poseidon2.hash_fields_with_trace_loop0_loop0 {name}Iter0 {name}State0 = _\n'
 for j in range(8):
  s+=f'  rw [poseidon2.hash_fields_with_trace_loop0_loop0,{name}Next{j}]\n  simp only [bind_tc_ok,aspis_core.field.M31.add,aspis_core.field.P,lift]\n  with_unfolding_all change poseidon2.hash_fields_with_trace_loop0_loop0 {name}Iter{j+1} {name}State{j+1} = _\n'
 s+=f'  rw [poseidon2.hash_fields_with_trace_loop0_loop0,{name}Next8]\n  with_unfolding_all rfl\n#print axioms absorb_{name}\n'
s+='end R1Z.PV_RunJoin_NullifierControl17\n'
p=L/'PV_RunJoin_NullifierControl17.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
