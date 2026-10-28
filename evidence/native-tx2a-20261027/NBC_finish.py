"""Read-only source/cache audit, then cleanup only this job's build outputs."""
from pathlib import Path
import json,subprocess,shlex,time,hashlib
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-native-tx2a-20261027'
manifest=json.loads((E/'NBC_SCRATCH_MANIFEST.json').read_text())
modules=json.loads((E/'NBC_TARGETS.json').read_text())['functions']
code=f'''from pathlib import Path
import json,hashlib,shutil
b=Path({B!r});s=b/'NBC_src';manifest={manifest!r};members={modules!r}
def pin(p):return dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
errors=[];modified=[]
for n,h in manifest.items():
 p=s/n
 if not p.is_file():errors.append(['missing',n]);continue
 if pin(p)['sha256']!=h:modified.append(n)
expected_modified=['crates/aspis-core/src/field/wide_exact.rs','crates/aspis-r1-cost-probe/src/verifier.rs','programs/r1-cost-probe/src/lib.rs']
assert sorted(modified)==sorted(expected_modified),(modified,expected_modified)
for n in modified:assert (s/n).read_text().endswith('\\n#[cfg(kani)]\\nmod NBC_runtime;\\n'),n
added=sorted(str(p.relative_to(s)) for p in s.rglob('*') if p.is_file() and str(p.relative_to(s)) not in manifest)
expected_added=['crates/aspis-core/src/field/wide_exact/NBC_runtime.rs','crates/aspis-r1-cost-probe/src/verifier/NBC_runtime.rs','programs/r1-cost-probe/src/NBC_runtime.rs']
assert added==sorted(expected_added),added
bodies={{f['id']:hashlib.sha256((s/f['file']).read_bytes()[f['body_start_byte']:f['body_end_byte']]).hexdigest() for f in members}}
assert all(bodies[f['id']]==f['body_sha256'] for f in members),'member body drift'
cache=Path('/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027')
roots=[cache,Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'),Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects'),Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
names=set()
for r in roots:
 for p in [r/'Aeneas.olean']+list((r/'Aeneas').rglob('*.olean')):
  if p.is_file():names.add(str(p.relative_to(r)))
selected={{n:next(r/n for r in roots if (r/n).is_file()) for n in names}}
scopes=[]
for p in b.glob('NBC_[KL]*/receipt.json'):
 r=json.loads(p.read_text());cg=Path(r['cgroup']);assert not cg.exists() or not (cg/'cgroup.procs').read_text().strip(),str(cg)
 scopes.append(dict(attempt=r['attempt'],exit=r['exit_status'],terminal=True))
objects=[str(p) for p in b.rglob('*.olean')]
assert not objects,objects
out=dict(source=dict(expected_files=len(manifest),errors=errors,modified=modified,added=added,member_body_hashes=bodies,all_member_bodies_frozen=True),cache={{str(p):pin(p) for p in cache.rglob('*') if p.is_file()}},aeneas={{str(p):pin(p) for p in selected.values()}},tools={{str(p):pin(p) for p in [Path('/home/dombarker/.cargo/bin/cargo-kani'),Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')]}},scopes=scopes,private_lean_objects=objects)
assert not errors,errors
for name in ['NBC_target','NBC_tmp']:
 p=b/name
 if p.exists():shutil.rmtree(p)
out['cleanup']=dict(removed_build_outputs=['NBC_target','NBC_tmp'],persistent_cache_retained=True,frozen_source_scratch_retained=True,keys_deleted=False)
print(json.dumps(out))
'''
# Recovery of this cleanup is read-only; never repeat after a submitted transport failure.
r=subprocess.run(['ssh','-o','ConnectTimeout=15',H,'python3 -c '+shlex.quote(code)],capture_output=True,text=True)
(E/'NBC_TERMINAL_TRANSPORT.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout if r.returncode else 'see NBC terminal receipts',stderr=r.stderr))+'\n')
assert r.returncode==0,'recover terminal cleanup read-only; no resubmission'
out=json.loads(r.stdout)
for k,n in [('source','NBC_SOURCE_AUDIT.json'),('cache','NBC_CACHE_END.json'),('aeneas','NBC_LIBRARY_END.json'),('tools','NBC_TOOL_PINS.json')]:
 (E/n).write_text(json.dumps(out[k],indent=2)+'\n')
start=json.loads((E/'NBC_CACHE_START.json').read_text())
assert all(out['cache'].get(k)==v for k,v in start.items()),'preexisting persistent object changed'
assert json.loads((E/'NBC_LIBRARY_START.json').read_text())==out['aeneas'],'resolved Aeneas objects changed'
(E/'NBC_TERMINAL_HOST.json').write_text(json.dumps({k:v for k,v in out.items() if k not in ['source','cache','aeneas','tools']},indent=2)+'\n')
print(json.dumps(dict(initial_cache_files=len(start),terminal_cache_files=len(out['cache']),all_initial_cache_files_unchanged=True,all_aeneas_pins_unchanged=True,scopes=out['scopes'],cleanup=out['cleanup']),indent=2))
