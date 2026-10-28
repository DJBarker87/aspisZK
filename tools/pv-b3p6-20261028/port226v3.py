"""B1/import-and-unused-metadata port of pinned v3 emission, never body edits."""
from pathlib import Path
import hashlib,json,re
D=Path('evidence/pv-b3p6-20261028');raw=D/'raw226-v3';out=D/'lean'
t=(raw/'Types.lean').read_text();f=(raw/'Funs.lean').read_text()
assert 'namespace PV_B3P_226V3' in t and 'namespace PV_B3P_226V3' in f
assert 'def reference226.public_bytes' in f
assert 'def reference226.chunk8' in f and 'def reference226.project_frontier_level' not in f
assert not re.search(r'index_mut|iter_mut|next_back|index_mut_back',f)
assert 'read_discriminant' not in f
pt=t.replace('import Aeneas\n','import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n')
pt=pt.replace('@[discriminant isize, rust_type','@[rust_type').replace('@[discriminant isize]\n','')
assert 'discriminant' not in pt
pf=f.replace('import Aeneas\n','import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n')
pf=re.sub(r'^import \S+\.Types$', 'import PV_B3P_BytesV3Types226',pf,flags=re.M)
names=re.findall(r'^def (\S+)',f,re.M)
pf+='\n'+''.join('#print axioms PV_B3P_226V3.'+n+'\n' for n in names)
for n,s in [('PV_B3P_BytesV3Types226',pt),('PV_B3P_BytesV3Emission226',pf)]:
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b',s)
 (out/(n+'.lean')).write_text(s)
record={'raw_types_sha256':hashlib.sha256(t.encode()).hexdigest(),'raw_funs_sha256':hashlib.sha256(f.encode()).hexdigest(),'ported_types_sha256':hashlib.sha256(pt.encode()).hexdigest(),'ported_funs_sha256':hashlib.sha256(pf.encode()).hexdigest(),'body_edits':False,'edits':['B1 imports','private Types module import','unused discriminant metadata only','axioms print commands appended'],'mutable_writes':0,'discarded_backward_continuations':0,'declarations':names,'native_emission_differential':'pending; no source-fidelity credit claimed'}
(D/'port226v3.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'declarations':len(names),'mutable_writes':0,'body_edits':False}))
