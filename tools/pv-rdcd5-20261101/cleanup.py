"""Remove only this completed task's verified compiler caches; retain evidence/source."""
from pathlib import Path
import json,shutil,re,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd5-20261101');assert D.resolve()==D
assert json.load(open(D/'coherence-result.json'))['status'].startswith('PASS:')
for n in [78297,78298,78299]:
 t=(D/f'lean-{n}/time.log').read_text();assert re.search(r'Exit status:\s*0\s*$',t),n
 assert 'sorryAx' not in (D/f'lean-{n}/output.log').read_text(),n
# The final manifest adds three new audit objects to the previously checked
#70-module cohort. Verify their actual final-launch fingerprint before deletion.
release=json.load(open(D/'release-object-inputs.json'));added={}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for module,pin in release['final_launch_dependencies'].items():
 assert sha(Path(pin['object_path']))==pin['object_sha256'],module
for pin in release['audits']:
 module=pin['module'];source=D/'lean-sources'/(module+'.lean');obj=D/'lean-objects'/(module+'.olean')
 assert sha(source)==pin['source_sha256'],module
 added[module]=dict(object_sha256=sha(obj),object_path=str(obj),source_sha256=sha(source),source_revision=pin['source_revision'],receipt='lean-'+str(pin['attempt'])+'/receipt.json')
(D/'release-object-addendum.json').write_text(json.dumps(dict(audit_modules=added,final_launch_dependencies=len(release['final_launch_dependencies']),cohort='70 focused/coherent objects plus3 audited release objects; all actual final-launch imports still match',scope='new release-object addendum, no second manifest replay'),indent=2)+'\n')
inventory=[]
for name in ['lean-objects','external-objects']:
 p=D/name;assert p.parent==D and p.is_dir() and not p.is_symlink()
 files=[q for q in p.rglob('*') if q.is_file()]
 assert not any(q.is_symlink() for q in p.rglob('*'))
 unexpected=[str(q) for q in files if not q.name.endswith(('.olean','.ir','.olean.private','.olean.server','.ilean','.trace','.hash'))]
 assert not unexpected,('keep caches: unexpected file types',unexpected)
 inventory.append(dict(path=str(p),file_count=len(files),bytes=sum(q.stat().st_size for q in files),classification='only compiled Lean/external objects and companions; no wallet/account keys or source/evidence'))
for x in inventory:shutil.rmtree(x['path'])
for x in inventory:assert not Path(x['path']).exists()
(D/'cleanup-result.json').write_text(json.dumps(dict(deleted=inventory,retained='all sources, receipts, source bindings, manifests and proofs; all keys unchanged',hashes='coherence/object hashes are measured pre-cleanup values; compiled caches no longer available',status='PASS: own task caches only'),indent=2)+'\n')
print('Removed only own compiler caches:',sum(x['bytes'] for x in inventory),'bytes; source/evidence/keys retained')
