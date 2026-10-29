from pathlib import Path
D=Path('evidence/pv-b3q-20261029/lean')
seeds=[0,1,7,19,2147483646,2147483647,2147483648,4294967295,0x80000000,0xabcdef01]
rot=lambda n,k:((n<<k)|(n>>(32-k)))&0xffffffff
q=lambda n:'{ c0 := { a := '+str(n)+'#u32, b := '+str(rot(n,7))+'#u32 }, c1 := { a := '+str(rot(n,13))+'#u32, b := '+str(rot(n,23))+'#u32 } }'
for chunk in range(2):
 name='PV_B3Q_MatrixRawFixture'+str(chunk)
 s='import PV_B3P_P227_01\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_227\nset_option autoImplicit false\n'
 for case in range(chunk*5,chunk*5+5):
  seed=seeds[case];s+='def matrix'+str(case)+' : Result (Array (Array U64 3#usize) 3#usize) := do\n let sums := Array.repeat 3#usize (Array.repeat 3#usize 0#u64)\n'
  for i in range(3):s+=' let left'+str(i)+' ← reference_field.PreparedQm31Multiplier.new ('+q((seed+i*131)&0xffffffff)+')\n'
  for i in range(3):s+=' let sums'+str(i+1)+' ← reference_field.accumulate_prepared227 '+('sums'if i==0 else'sums'+str(i))+' ('+q((seed+i*173)&0xffffffff)+') left'+str(i)+'\n'
  s+=' .ok sums3\n#eval "raw_matrix:'+str(case)+'=" ++ (match matrix'+str(case)+' with | .ok xs => reprStr (xs.val.flatMap (fun row => row.val.map (fun x => x.val))) | .fail _ => "FAIL" | .div => "DIV")\n'
 s+='end '+name+'\n';(D/(name+'.lean')).write_text(s)
