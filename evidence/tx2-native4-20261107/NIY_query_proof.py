from pathlib import Path
E=Path(__file__).resolve().parent;p=E/'NIY_QueryRead.lean';s=p.read_text();a=s.index(' := by\n',s.index('theorem continuation'))+len(' := by\n');b=s.index('\n#print axioms',a)
ops=[]
for i in range(22):ops += [f'let (a{i+5}, r{i+13}) ← raw r{i+12}',f'let i{i+8} ← lift (core.num.U32.from_le_bytes a{i+5})']
arr='(Array.make 22#usize ['+', '.join('i'+str(i) for i in range(8,30))+'])'
proof=' unfold read22\n'
for i in range(44):
 rem='\n'.join('   '+x for x in ops[i:]);proof+=f' change (do\n   let p ← (do\n'+ '\n'.join('    '+x for x in ops[i:])+f'\n    ok ({arr},r34))\n   next p.1 p.2)=(do\n{rem}\n   next {arr} r34)\n'
 proof+=' with_unfolding_all rw [assoc]\n apply NIL_ResultCases.bind_congr\n'
 if i%2==0:proof+=f' rintro ⟨a{i//2+5},r{i//2+13}⟩\n'
 else:proof+=f' intro i{i//2+8}\n'
proof+=' rfl\n';p.write_text(s[:a]+proof+s[b:])
