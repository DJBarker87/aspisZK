from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent
pins=json.loads((E/'NDN_AUDIT_PINS.json').read_text())['selected_objects']
code='''from pathlib import Path
import json,hashlib,shutil,os
b=Path('/home/dombarker/project-offloads/codex-cx-native-front2b-20261028');pins=json.loads(PAYLOAD)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
errors=[p for p,v in pins.items() if not Path(p).is_file() or sha(Path(p))!=v['sha256']]
assert not errors,errors[:5]
cache=b.parent/'codex-cx-front2-cache-20261028'/'NDN_retained';assert not cache.exists();shutil.copytree(b/'NDN_objects',cache)
objects={str(p.relative_to(cache)):dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size) for p in cache.rglob('*') if p.is_file()}
for n,v in objects.items():assert sha(b/'NDN_objects'/n)==v['sha256']
removed={};retained=[]
for n in ['NDN_target','NDN_ref_target','NDN_tmp','NDN_objects']:
 p=b/n
 if not p.exists():continue
 assert p.is_dir() and not p.is_symlink(),n
 sensitive=[str(q) for q in p.rglob('*') if q.is_file() and (q.name in ['id.json','keypair.json','wallet.json'] or q.name.endswith('-keypair.json'))]
 if sensitive:retained.append(dict(path=str(p),reason='potential key files; keep',files=sensitive));continue
 removed[n]=sum(q.stat().st_size for q in p.rglob('*') if q.is_file());shutil.rmtree(p)
tools={}
for p in [Path('/home/dombarker/.cargo/bin/cargo-kani'),Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'),Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon'),Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended')]:
 tools[str(p)]=dict(resolved=str(p.resolve()),sha256=sha(p),bytes=p.stat().st_size)
r=dict(selected_object_pins_verified=len(pins),errors=errors,retained_cache=str(cache),objects=objects,removed_build_bytes=removed,retained_for_key_safety=retained,tools=tools,disk_free_bytes=shutil.disk_usage(b).free,source_workspaces_and_prior_cache_untouched=True,no_prover_or_rust_command=True)
(b/'NDN_FINAL_HOST.json').write_text(json.dumps(r,indent=2)+'\\n');print(json.dumps(r))
'''.replace('PAYLOAD',repr(json.dumps(pins)))
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
(E/'NDN_CLEANUP_TRANSPORT.log').write_text(r.stderr)
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'NDN_FINAL_HOST.json').write_text(json.dumps(x,indent=2)+'\n')
print('Verified',x['selected_object_pins_verified'],'object pins; retained',len(x['objects']),'objects; removed own rebuildable outputs only')
