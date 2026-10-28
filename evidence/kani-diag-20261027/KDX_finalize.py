from pathlib import Path
import json,sys,subprocess,hashlib,difflib
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import KDX_host as h
r=h.remote_py(f'''from pathlib import Path
import json,hashlib,subprocess,re,shutil
b=Path({h.B!r});out={{}}
for label,root in [('cache',{h.CACHE!r}),('coherent',{(h.C+'/objects')!r})]:
 out[label]={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in Path(root).rglob('*.olean')}}
# Retain the only changed failed-extraction file as text for a historical patch.
p=b/'KDX_K006/sources/KDX_src/crates/aspis-r1-cost-probe/src/KDX_R_LPm_K001.rs'
failed=p.read_text()
rows=subprocess.check_output(['ps','-eo','pid=,args='],text=True).splitlines()
live=[x for x in rows if re.search(r'^\\s*\\d+ (?:python3 S2W_(?:run|lean)_host.py KDX_|[^ ]*cbmc .*codex-cx-kani-diag)',x)]
assert not live,live
cleanup=[]
for name in ['KDX_target','KDX_tmp']:
 p=b/name
 if p.exists():shutil.rmtree(p);cleanup.append(str(p))
print(json.dumps(dict(pins=out,failed_module=failed,cleanup=dict(live_own_scopes=live,removed=cleanup,persistent_cache_retained=Path({h.CACHE!r}).is_dir(),keys_touched=False))))''');assert r.returncode==0,r.stderr
d=json.loads(r.stdout);(E/'KDX_FINAL_HOST_PINS.json').write_text(json.dumps(d['pins']))
initial=json.loads((E/'KDX_INITIAL_HOST_PINS.json').read_text());delta={}
for kind,old in initial.items():
 new=d['pins'][kind];delta[kind]=dict(changed={p:dict(before=old[p],after=new.get(p)) for p in old if old[p]!=new.get(p)},added={p:new[p] for p in new if p not in old})
(E/'KDX_PIN_COMPARISON.json').write_text(json.dumps(delta,indent=2)+'\n');(E/'KDX_CLEANUP.json').write_text(json.dumps(d['cleanup'],indent=2)+'\n')
new=(E/'KDX_R_LPm_K001.rs.txt').read_text()
(E/'KDX_EXTRACTOR_REPAIR.patch').write_text(''.join(difflib.unified_diff(d['failed_module'].splitlines(True),new.splitlines(True),fromfile='a/crates/aspis-r1-cost-probe/src/KDX_R_LPm_K001.rs',tofile='b/crates/aspis-r1-cost-probe/src/KDX_R_LPm_K001.rs')))
print(json.dumps({'cleanup':d['cleanup'],'object_changes':{k:len(v['changed']) for k,v in delta.items()},'object_additions':{k:len(v['added']) for k,v in delta.items()}}))
