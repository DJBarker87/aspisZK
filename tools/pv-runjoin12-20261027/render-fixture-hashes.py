"""Bounded fixture hash certificate: numeric data are checked one round at a time.
No records extraction/source identity/compiler success is asserted by generation.
"""
from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin12-20261027';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
source=E/'pv12-fixture-hash-states-01/out.log';states={}
for line in source.read_text().splitlines():
 try:a,b,rest=line.split(' ',2);a=int(a);b=int(b);xs=json.loads(rest)
 except (ValueError,json.JSONDecodeError):continue
 assert len(xs)==16 and all(type(v)==int and 0<=v<2147483647 for v in xs)
 assert (a,b) not in states;states[a,b]=xs
assert set(states)=={(a,b) for a in range(6) for b in range(24)}
assert states[0,0]==[11+17*i for i in range(8)]+[0x41530001,8]+[0]*6
assert states[1,0]==states[0,23][:8]+[0x41530003,18]+[0]*6
for cell,chunk in [(2,[1000,77]+[101+17*i for i in range(6)]),(3,[203,220]+[0]*6),(5,[101+17*i for i in range(8)])]:
 assert states[cell,0]==[(x+y)%2147483647 for x,y in zip(states[cell-1,23],chunk+[0]*8)]
assert states[4,0]==[11+17*i for i in range(8)]+[0x41530002,16]+[0]*6
assert states[3,23][:8]==[2028667570,45893279,894642502,1930282162,1562116262,823639309,745717450,1034934647]
assert states[5,23][:8]==[8526811,109678668,1639079956,402852,1893371776,347120802,331397657,1970188241]
vec=lambda xs:'!['+','.join(map(str,xs))+']'
def idx(j,n):return '0' if j==0 else '('+'Fin.succ ('*j+f'(0 : Fin {n-j})'+')'*j+')'
header='set_option autoImplicit false\nnoncomputable section\nnamespace R1Z.PV_RunJoin_FixtureHashModel\nopen R0P\n'
end='end R1Z.PV_RunJoin_FixtureHashModel\n'
text='import R1Z.PV_RunJoin_FixtureRecords\n\n/-! Literal round states only; no source or generator equality is assumed. -/\n'+header+'abbrev Scalar := PV_RunJoin_FixtureRecords.M\n'
for a in range(6):
 for b in range(24):text+=f'def s_{a}_{b} : Fin 16 → Scalar := {vec(states[a,b])}\n'
text+='#print axioms s_0_0\n'+end
files={'PV_RunJoin_FixtureHashData.lean':text}
for a in range(6):
 for group,(lo,hi) in enumerate([(1,7),(7,13),(13,19),(19,24)]):
  text='import R1Z.PV_RunJoin_FixtureHashData\n\n/-! Each equation checks exactly one bounded round. No recurrence is unfolded. -/\n'+header
  for b in range(lo,hi):
   if b==1:expr=f'poseidonExternalLinear s_{a}_0'
   elif b<=5:expr=f'poseidonFullRound s_{a}_{b-1} (poseidonExternalInitial {idx(b-2,4)})'
   elif b<=19:expr=f'poseidonInternalRound s_{a}_{b-1} (poseidonInternalConstants {idx(b-6,14)})'
   else:expr=f'poseidonFullRound s_{a}_{b-1} (poseidonExternalFinal {idx(b-20,4)})'
   text+=f'theorem round_{a}_{b} : {expr} = s_{a}_{b} := by\n  funext i\n  fin_cases i <;> rfl\n#print axioms round_{a}_{b}\n'
  files[f'PV_RunJoin_FixtureHashRound{a}_{group}.lean']=text+end
 text=''.join(f'import R1Z.PV_RunJoin_FixtureHashRound{a}_{g}\n' for g in range(4))+header
 text+=f'theorem permutation_{a} : poseidonPermutation s_{a}_0 = s_{a}_23 := by\n  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]\n'
 text+='  rw ['+','.join(f'round_{a}_{b}' for b in range(1,24))+']\n'
 text+=f'#print axioms permutation_{a}\n'+end
 files[f'PV_RunJoin_FixtureHashCell{a}.lean']=text
for name,text in files.items():
 if '--check' in sys.argv:assert (L/name).read_text()==text,name
 else:(L/name).write_text(text)
(E/'fixture-hash-generation.json').write_text(json.dumps(dict(classification='mathematical fixture hash data; no source mapper, native compiler, or deployed equation',input_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),cells=6,round_equations=138,max_recurrence_depth_per_equation=1,exceptional_shapes='sparse initial sponge states explicitly checked by the later absorb-init lemmas; all subsequent cells apply one named round equation',files={n:hashlib.sha256(t.encode()).hexdigest() for n,t in files.items()}),indent=2)+'\n')
print('fixture hash generation/check passed')
