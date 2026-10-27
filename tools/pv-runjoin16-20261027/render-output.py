"""Output/append candidate round certificates. Every equation covers one round;
no hash recurrence is normalized. A --check run performs no writes."""
from pathlib import Path
import json,hashlib,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin16-20261027';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';source=E/'pv16-output-states-01/out.log';states={}
for line in source.read_text().splitlines():
 try:a,b,rest=line.split(' ',2);a=int(a);b=int(b);xs=json.loads(rest)
 except (ValueError,json.JSONDecodeError):continue
 assert len(xs)==16 and all(type(x)==int and 0<=x<2147483647 for x in xs)
 assert (a,b) not in states;states[a,b]=xs
assert set(states)=={(a,b) for a in range(30,81) for b in range(24)}
vec=lambda xs:'!['+','.join(map(str,xs))+']'
def idx(j,n):return '0' if j==0 else '('+'Fin.succ ('*j+f'(0 : Fin {n-j})'+')'*j+')'
header='set_option autoImplicit false\nnoncomputable section\nnamespace R1Z.PV_RunJoin_OutputModel16\nopen R0P\n'
end='end R1Z.PV_RunJoin_OutputModel16\n'
s='import R1Z.PV_RunJoin_FixtureRecords\n'+header+'abbrev Scalar := PV_RunJoin_FixtureRecords.M\n'
for (a,b),xs in sorted(states.items()):s+=f'def s_{a}_{b} : Fin 16 → Scalar := {vec(xs)}\n'
s+='#print axioms s_30_0\n'+end
files={'PV_RunJoin_OutputData16.lean':s}
# Three sponge blocks per note; output pair nodes; then four bounded append groups.
groups=[('Recipient16',range(30,33)),('TransferChange16',range(33,36)),('WithdrawalChange16',range(36,39)),('OutputPairs16',range(39,41))]+[(f'Append{g}16',range(41+10*g,51+10*g)) for g in range(4)]
for label,cells in groups:
 s='import R1Z.PV_RunJoin_OutputData16\n'+header
 for a in cells:
  for b in range(1,24):
   if b==1:expr=f'poseidonExternalLinear s_{a}_0'
   elif b<=5:expr=f'poseidonFullRound s_{a}_{b-1} (poseidonExternalInitial {idx(b-2,4)})'
   elif b<=19:expr=f'poseidonInternalRound s_{a}_{b-1} (poseidonInternalConstants {idx(b-6,14)})'
   else:expr=f'poseidonFullRound s_{a}_{b-1} (poseidonExternalFinal {idx(b-20,4)})'
   s+=f'theorem round_{a}_{b} : {expr} = s_{a}_{b} := by\n  funext i\n  fin_cases i <;> rfl\n#print axioms round_{a}_{b}\n'
  s+=f'theorem permutation_{a} : poseidonPermutation s_{a}_0 = s_{a}_23 := by\n  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]\n  rw ['+','.join(f'round_{a}_{b}' for b in range(1,24))+']\n'+f'#print axioms permutation_{a}\n'
  if a>=39:
   left=vec(states[a,0][:8]);right=vec(states[a,0][8:15]+[(states[a,0][15]-0x41531005)%2147483647]);out=vec(states[a,23][:8])
   s+=f'''theorem node_{a} : nodeCompress ({left} : Fin 8 → Scalar) {right} = {out} := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then ({left} : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then ({right} : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else ({right} : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_{a}_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_{a}]
  funext i
  fin_cases i <;> rfl
#print axioms node_{a}
'''
 s+=end;files['PV_RunJoin_Output'+label+'.lean']=s
receipt=dict(input_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),cells=51,rounds=1173,maximum_recurrence_depth=1,exceptional_shapes='named hi for every node start; each sponge start to be bound by note init/absorb lemmas',next_consumer='PV_RunJoin_OutputValues16 and native compiler recipient/change/output-pair/append checks',files={n:hashlib.sha256(s.encode()).hexdigest() for n,s in files.items()})
candidate=E/'candidate-certificates'
if '--check' not in sys.argv:candidate.mkdir(exist_ok=True)
receipt['destinations']={n:str((candidate/(n+'.txt') if ('Append' in n or 'Pairs' in n) else L/n).relative_to(R)) for n in files}
for n,s in files.items():
 dest=R/receipt['destinations'][n]
 if '--check' in sys.argv:assert dest.read_text()==s,n
 else:dest.write_text(s)

if '--check' in sys.argv:assert json.loads((E/'output-generation.json').read_text())==receipt
else:(E/'output-generation.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('output generation/check passed')
