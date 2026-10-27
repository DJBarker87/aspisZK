"""Emit named single-round mathematical path certificates; --check never mutates."""
from pathlib import Path
import json,sys,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin16-20261027';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
source=E/'pv16-path-states-01/out.log';states={}
for line in source.read_text().splitlines():
 try:a,b,rest=line.split(' ',2);a=int(a);b=int(b);xs=json.loads(rest)
 except (ValueError,json.JSONDecodeError):continue
 assert len(xs)==16 and all(type(v)==int and 0<=v<2147483647 for v in xs)
 assert (a,b) not in states;states[a,b]=xs
assert set(states)=={(a,b) for a in range(6,30) for b in range(24)}
vec=lambda xs:'!['+','.join(map(str,xs))+']'
def idx(j,n):return '0' if j==0 else '('+'Fin.succ ('*j+f'(0 : Fin {n-j})'+')'*j+')'
header='set_option autoImplicit false\nnoncomputable section\nnamespace R1Z.PV_RunJoin_PathModel16\nopen R0P\n'
end='end R1Z.PV_RunJoin_PathModel16\n'
s='import R1Z.PV_RunJoin_FixtureRecords\n'+header+'abbrev Scalar := PV_RunJoin_FixtureRecords.M\n'
for (a,b),xs in sorted(states.items()):s+=f'def s_{a}_{b} : Fin 16 → Scalar := {vec(xs)}\n'
s+='#print axioms s_6_0\n'+end
files={'PV_RunJoin_PathData16.lean':s}
for a in range(6,30):
 s='import R1Z.PV_RunJoin_PathData16\n'+header
 for b in range(1,24):
  if b==1:expr=f'poseidonExternalLinear s_{a}_0'
  elif b<=5:expr=f'poseidonFullRound s_{a}_{b-1} (poseidonExternalInitial {idx(b-2,4)})'
  elif b<=19:expr=f'poseidonInternalRound s_{a}_{b-1} (poseidonInternalConstants {idx(b-6,14)})'
  else:expr=f'poseidonFullRound s_{a}_{b-1} (poseidonExternalFinal {idx(b-20,4)})'
  s+=f'theorem round_{a}_{b} : {expr} = s_{a}_{b} := by\n  funext i\n  fin_cases i <;> rfl\n#print axioms round_{a}_{b}\n'
 s+=f'theorem permutation_{a} : poseidonPermutation s_{a}_0 = s_{a}_23 := by\n  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]\n  rw ['+','.join(f'round_{a}_{b}' for b in range(1,24))+']\n'
 left=vec(states[a,0][:8]);right=vec(states[a,0][8:15]+[(states[a,0][15]-0x41531005)%2147483647]);out=vec(states[a,23][:8])
 s+=f'''theorem node_{a} : nodeCompress ({left} : Fin 8 → Scalar) {right} = {out} := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then ({left} : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then ({right} : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else ({right} : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_{a}_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_{a}]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_{a}
#print axioms node_{a}
'''+end
 files[f'PV_RunJoin_PathCell{a:02d}16.lean']=s
# Explicit exceptional shape: no recurrence normalizations; every sparse starting cell is bound by hi.
receipt=dict(input_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),cells=24,rounds=552,maximum_recurrence_depth=1,exceptional_shapes='each sparse or exceptional node start uses its named hi equality and node theorem',next_consumer='PV_RunJoin_PathValues16 then native compiler path checks',files={n:hashlib.sha256(s.encode()).hexdigest() for n,s in files.items()})
for n,s in files.items():
 if '--check' in sys.argv:assert (L/n).read_text()==s,n
 else:(L/n).write_text(s)
if '--check' in sys.argv:assert json.loads((E/'path-generation.json').read_text())==receipt
else:(E/'path-generation.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('path generation/check passed')
