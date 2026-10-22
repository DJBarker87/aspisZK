from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent.parent
host='dombarker@100.108.41.90';R='/home/dombarker/project-offloads/codex-cx-prover-commit29-20261022'
subprocess.run(['scp','-r',host+':'+R+'/receipts',str(E)],check=True)
for name in ['step29-v1','step29-v2','step29-owned-v3','iteration29-v1','fields29-v1']:
 for suffix in ['-charon-inputs.json','-aeneas-inputs.json','-llbc.json']:
  subprocess.run(['scp',host+':'+R+'/'+name+suffix,str(E)],check=True)
for name in ['Types.lean','Funs.lean']:
 subprocess.run(['scp',host+':'+R+'/extraction/generated-iteration29-v1/AspisR1SemanticStep29/'+name,str(E/'extraction'/('iteration-v1-'+name+'.txt'))],check=True)
for name in ['Types.lean','Funs.lean']:
 subprocess.run(['scp',host+':'+R+'/extraction/generated-fields29-v1/AspisR1FiniteFields29/'+name,str(E/'extraction'/('fields29-v1-'+name+'.txt'))],check=True)
x=json.loads((E/'iteration29-v1-llbc.json').read_text());assert x['has_errors'] is False and x['opaque']==[]
fuel=json.loads((E/'fields29-v1-llbc.json').read_text());assert fuel['has_errors'] is False and fuel['opaque']==[]
(E/'extraction-status.json').write_text(json.dumps(dict(owned_reference=x,fueled_reference=fuel,opaque_cut_used=False,raw_text_retained=True,port='step-port.json; only nominal Error namespace in owner, retained dependencies with explicit signed shift-count compatibility annotation',source_identity={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path('crates/aspis-r1-cost-probe/src/sim.rs'),Path('crates/aspis-r1-cost-probe/src/r1_wire.rs')]},excluded=['step29-v1: borrowed field-validation extraction exception','step29-v2: opaque validation boundary; no native callee refinement claimed']),indent=2)+'\n')
