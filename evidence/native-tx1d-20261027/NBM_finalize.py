from pathlib import Path
import sys,json,subprocess,hashlib
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NBM_host as h
r=h.remote_py(f'''from pathlib import Path
import json,hashlib,subprocess,shutil,re
b=Path({h.B!r});out={{}}
for label,root in [('cache',{h.CACHE!r}),('coherent',{h.C!r}),('aeneas',{(h.C+'/objects/Aeneas')!r})]:
 out[label]={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in Path(root).rglob('*.olean')}}
p=Path({(h.C+'/objects/Aeneas.olean')!r});out['aeneas'][str(p)]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)
p=b/'NBM_FINAL_HOST_PINS.json';p.write_text(json.dumps(out))
k=Path('/home/dombarker/.kani/kani-0.67.0');tools={{}}
for name,cmd in [('kani',['/home/dombarker/.cargo/bin/cargo-kani','--version']),('kani-rustc',[str(k/'toolchain/bin/rustc'),'--version','--verbose']),('cargo',['/home/dombarker/.cargo/bin/cargo','--version']),('native-client-rustc',['/home/dombarker/.cargo/bin/rustc','+1.94.1','--version','--verbose'])]:
 r=subprocess.run(cmd,text=True,capture_output=True);tools[name]=dict(command=cmd,exit=r.returncode,stdout=r.stdout,stderr=r.stderr)
for name in ['bin/kani-driver','bin/kani-compiler','bin/cbmc','toolchain/bin/rustc']:
 p=k/name
 if p.is_file():tools[name]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)
# Retain hashes/sizes, never commit a binary.
binaries={{str(p.relative_to(b)):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in (b/'NBM_target').rglob('aspis_r1_cost_probe-*') if p.is_file() and p.stat().st_mode&0o111}}
rows=subprocess.check_output(['ps','-eo','args='],text=True).splitlines();live=[x for x in rows if re.match(r'^python3 S2W_(?:run|lean)_host[.]py NBM_',x.strip())];assert not live,live
for name in ['NBM_target','NBM_tmp']:
 p=b/name
 if p.exists():shutil.rmtree(p)
print(json.dumps(dict(pins=out,tools=tools,cleanup=dict(live_scopes=live,removed=['NBM_target','NBM_tmp'],persistent_cache_retained=Path({h.CACHE!r}).is_dir(),binaries=binaries))))
''');assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
(E/'NBM_FINAL_HOST_PINS.json').write_text(json.dumps(out.pop('pins'))+'\n')
(E/'NBM_TOOLS_AND_CLEANUP.json').write_text(json.dumps(out,indent=2)+'\n')
a=json.loads((E/'NBM_INITIAL_HOST_PINS.json').read_text());b=json.loads((E/'NBM_FINAL_HOST_PINS.json').read_text());changes={k:[n for n,x in d.items() if b[k].get(n)!=x] for k,d in a.items()}
assert not changes['coherent'] and not changes['aeneas'],changes
assert not any(Path(n).name.startswith('NBM_') for n in changes['cache']),changes
(E/'NBM_PIN_COMPARISON.json').write_text(json.dumps(dict(start={k:len(v) for k,v in a.items()},end={k:len(v) for k,v in b.items()},changed_or_removed_initial_objects=changes,concurrent_additions={k:sorted(set(b[k])-set(a[k])) for k in a}),indent=2)+'\n')
