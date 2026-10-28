from pathlib import Path
import sys,json,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];sys.path.insert(0,str(E));import NBV_host as h
assert len(list(E.glob('NBV_K[0-9][0-9][0-9]/receipt.json')))==50,'Native budget not yet used'
initial=json.loads((E/'NBV_INITIAL_HOST_PINS.json').read_text())
# Read-only process/object verification; cleanup only own rebuildable target/tmp.
r=h.remote_py(f'''from pathlib import Path
import json,hashlib,subprocess,shutil,re
b=Path({h.B!r});rows=subprocess.check_output(['ps','-eo','args='],text=True).splitlines()
live=[x for x in rows if re.match(r'^(?:/usr/bin/)?python3 S2W_(?:run|lean)_host[.]py NBV_',x.strip())]
assert not live,live
out={{'live_own_scopes':live,'objects':{{}}}}
for label,root in [('cache',{h.CACHE!r}),('coherent',{h.C!r}),('aeneas',{(h.C+'/objects/Aeneas')!r})]:
 out['objects'][label]={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in Path(root).rglob('*.olean')}}
p=Path({(h.C+'/objects/Aeneas.olean')!r});out['objects']['aeneas'][str(p)]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)
s=b/'NBV_src';names=['lib.rs','candidate.rs','multiproof.rs','NBV_multiproof.rs','NBV_keys.rs','NBV_replay_keys.rs','NBV_leaf_rows.rs','NBV_posthash.rs','NBV_row_windows.rs','NBV_parent.rs']
out['final_sources']={{'crates/aspis-r1-cost-probe/src/'+n:(s/'crates/aspis-r1-cost-probe/src'/n).read_text() for n in names}}
out['lock_sha256']=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest()
out['stub_sha256']=hashlib.sha256((s/'KMX_stubs.rs').read_bytes()).hexdigest()
out['copy_patch_sha256']=hashlib.sha256((b/'NBV_KMX_copy_stubs.patch').read_bytes()).hexdigest()
out['cleanup']={{}}
for name in ['NBV_target','NBV_tmp']:
 p=b/name;assert p.parent==b and not p.is_symlink()
 if p.exists():
  out['cleanup'][name]={{'files':sum(x.is_file() for x in p.rglob('*')),'bytes':sum(x.stat().st_size for x in p.rglob('*') if x.is_file())}}
  shutil.rmtree(p)
 out['cleanup'][name]['removed']=not p.exists()
out['cache_retained']=Path({h.CACHE!r}).is_dir()
print(json.dumps(out))''');assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
sources=out.pop('final_sources')
(E/'NBV_FINAL_HOST_PINS.json').write_text(json.dumps(out,indent=2)+'\n')
comparison={}
for group in ['cache','coherent','aeneas']:
 old=initial[group];now=out['objects'][group]
 changed={n:dict(before=v,after=now.get(n)) for n,v in old.items() if now.get(n)!=v}
 assert not changed,(group,changed)
 comparison[group]=dict(initial=len(old),final=len(now),changed=changed,added={n:v for n,v in now.items() if n not in old})
(E/'NBV_PIN_COMPARISON.json').write_text(json.dumps(comparison,indent=2)+'\n')
patch=''
for n,new in sources.items():
 old=(R/n).read_text() if (R/n).exists() else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n if old else '/dev/null',tofile='b/'+n))
(E/'NBV_complete_harness.patch').write_text(patch)
assert out['copy_patch_sha256']==initial['copy_patch_sha256']
assert out['lock_sha256']==initial['lock_sha256']
print(json.dumps(dict(counts={g:(v['initial'],v['final']) for g,v in comparison.items()},cleanup=out['cleanup'],patch_sha256=hashlib.sha256(patch.encode()).hexdigest())))
