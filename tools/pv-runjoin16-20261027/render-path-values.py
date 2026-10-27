"""Compose named node equations. Explicit extensional input equalities prevent
conversion from unfolding a concrete permutation. --check is read-only."""
from pathlib import Path
import json,sys,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin16-20261027';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';states={}
for line in (E/'pv16-path-states-01/out.log').read_text().splitlines():
 try:a,b,rest=line.split(' ',2);states[int(a),int(b)]=json.loads(rest)
 except (ValueError,json.JSONDecodeError):pass
vec=lambda xs:'!['+','.join(map(str,xs))+']'
files={}
for name,limit in [('PathFirst16',1),('PathValues16',24)]:
 s=''.join(f'import R1Z.PV_RunJoin_PathCell{a:02d}16\n' for a in range(6,6+limit))+'import R1Z.PV_RunJoin_FixtureInputCommitment\nset_option autoImplicit false\nnoncomputable section\nnamespace R1Z.PV_RunJoin_'+name+'\nopen R0P PV_RunJoin_PathModel16\nattribute [local irreducible] nodeCompress poseidonPermutation\nlocal notation "leaf" => digestOf PV_RunJoin_FixtureHashModel.s_3_23\n'
 for n in range(1,limit+1):
  a=n+5;out=vec(states[a,23][:8]);left=vec(states[a,0][:8]);right=vec(states[a,0][8:15]+[(states[a,0][15]-0x41531005)%2147483647])
  s+=f'''theorem prefix_{n} : merkleRootAux leaf PV_RunJoin_FixtureRecords.path {n} = ({out} : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show {n-1} < 24 by decide)'''+(f',prefix_{n-1}' if n>1 else '')+f''']
  change nodeCompress _ _ = _
  trans nodeCompress ({left} : Fin 8 → Scalar) {right}
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_{a}
#print axioms prefix_{n}
'''
 s+='end R1Z.PV_RunJoin_'+name+'\n';files['PV_RunJoin_'+name+'.lean']=s
for n,s in files.items():
 if '--check' in sys.argv:assert (L/n).read_text()==s,n
 else:(L/n).write_text(s)
receipt=dict(previous_failure='50649: path composition conversion timeout at200000heartbeats',replacement='opaque nodeCompress/poseidonPermutation; two finite extensional input equalities; named node theorem',files={n:hashlib.sha256(s.encode()).hexdigest() for n,s in files.items()})
if '--check' in sys.argv:assert json.loads((E/'path-values-generation.json').read_text())==receipt
else:(E/'path-values-generation.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('path values generation/check passed')
