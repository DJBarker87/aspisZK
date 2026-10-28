"""One assigned focused proof job via the unchanged capped scope/run2 tools."""
from pathlib import Path
import subprocess,sys,json,hashlib,re
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-fxio-20261028'
D='/home/dombarker/project-offloads/codex-pv-fxio-20261028';H='dombarker@100.108.41.90'
n=int(sys.argv[1]);m=sys.argv[2]
assert 35800<=n<=35899 and m.startswith('R1Z/PV_FXI_')
assert n<35897 or ('Audit' in m or 'Replay' in m)
p=R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean')
assert p.exists(); assert json.loads((E/'external-verification.json').read_text())['ok']
assert not (E/f'lean-{n}/receipt.json').exists()
# New proof source is tracked at HEAD under h5; never select an object from a sibling job.
b=subprocess.check_output(['git','show','HEAD:'+str(p.relative_to(R))]);assert b==p.read_bytes()
meta=dict(id=n,module=m,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_path=str(p.relative_to(R)),source_blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p.relative_to(R))],text=True).strip(),source_sha256=hashlib.sha256(b).hexdigest(),external_manifest_sha256=hashlib.sha256((E/'external-object-manifest.json').read_bytes()).hexdigest())
assert json.loads((E/f'{n}-id-preflight.json').read_text())['unused'] is True
meta['deps_fingerprint']=hashlib.sha256((E/'external-verification.json').read_bytes()).hexdigest()
meta['imported_external_objects']=['Init (all 5673 external objects verified before compile)']
meta['reused_project_objects']=[]
(E/f'{n}-source.json').write_text(json.dumps(meta,indent=2)+'\n')
# Upload only after the separate recorded successful admission check.
upload=json.loads((E/'source-upload-04.json').read_text())
assert upload[D+'/lean-sources/'+m+'.lean']==meta['source_sha256']
# The recorded SSH-stdin upload was hash-checked in the private directory;
# do not need a second transport to copy the same source again.
B='/home/dombarker/project-offloads'
cmd=['timeout','900','python3',B+'/aspis-fs-generic-20261006/evidence/run2.py',D+'/env-J.json',D+'/lean-objects',D+'/lean-sources',D+'/lean-objects/'+m+'.olean',D+'/lean-sources/'+m+'.lean','7000']
r=subprocess.run([sys.executable,str(R/'tools/pv-fxio-20261028/scope.py'),f'lean-{n}','compilation of '+m,*cmd])
q=E/f'lean-{n}/receipt.json'
if q.exists():
 j=json.loads(q.read_text());j.update(meta)
 log=(q.parent/'output.log').read_text()
 j['axioms']=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log,re.S)
 q.write_text(json.dumps(j,indent=2)+'\n');print(log)
sys.exit(r.returncode)
