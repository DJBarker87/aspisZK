"""Standalone raw-carrier sampler closure; no ProverRwFull carrier substitution.
All source/pure proofs are preserved except systematic private namespace/type aliases.
"""
from pathlib import Path
import re,json,hashlib,sys
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');E=Path('evidence/pv-batch2-20261027/batch2c');seen=set();order=[];ext=set()
def visit(n):
 if n in seen:return
 seen.add(n);p=L/(n+'.lean');s=p.read_text()
 for i in re.findall(r'^import (\S+)',s,re.M):
  if i.startswith('R1Z.PV_B2_'):visit(i[4:])
  elif i not in ['R1Z.ProverRwFullTypes','R1Z.ProverRwSamplerArithmetic']:ext.add(i)
 order.append((p,s))
# Raw carrier definitions must precede the normalized sampler aliases.
visit('PV_B2_RawSamplerTypes');visit('PV_B2_ordinary_sample');visit('PV_B2_GammaCarrier')
body=[]
for p,s in order:
 s=re.sub(r'^import .*\n','',s,flags=re.M)
 s=s.replace('ProverRwFull.','PV_B2_249.').replace('PV_B2_','PV_B2_C_').replace('ProverRwSamplerArithmetic','PV_B2_C_MachineArithmetic')
 body.append('-- Component '+p.name+'\nsection\n'+s+'\n'+('end\n'*len(re.findall(r'^noncomputable section$',s,re.M)))+'end\n')
s=''.join('import '+i+'\n' for i in sorted(ext))+'import R1Z.PV_B2_C_MachineArithmetic\n'+''.join(body)
p=L/'PV_B2_C_SamplerEnvironment.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
j=dict(external_imports=sorted(ext),systematic_changes=['private namespaces','ProverRwFull field type aliases point to exact raw PV_B2_C_249 extracted carriers','scalar facts use independent pinned-Aeneas machine arithmetic proofs'],components={str(p):hashlib.sha256(s.encode()).hexdigest() for p,s in order},output_sha256=hashlib.sha256(s.encode()).hexdigest(),scope='raw emission/source/value laws only; no native original/copy or callback installation credit')
p=E/'SAMPLER-PREFLIGHT.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==j
else:p.write_text(json.dumps(j,indent=2)+'\n')
