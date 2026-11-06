"""Owned runner: frozen offline graph, exact KMX, source erasure, isolated target."""
from NJY_transport import *
from NJY_inspect import inputs,Q
import hashlib,lzma,base64,shlex
sha=lambda b:hashlib.sha256(b).hexdigest()
def baseline():
 files=inputs('NJQ_K006');x=json.loads((Q/'NJQ_K006.json').read_text())
 # Remove the historical identity annotation/module when testing independent members.
 for parent in ['format.rs','verifier_registry.rs','pair_forest_accounts.rs']:
  n='crates/aspis-statement/src/pool_v1/'+parent
  files['NIJ_src/'+n]=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],text=True)
 files.pop('NJQ_isolation.py',None)
 x['native_command']=[s.replace('/codex-cx-tx2-decoders2-20261107/','/codex-cx-tx2-decoders3-20261107/').replace('/NJQ_target','/NJY_target') for s in x['native_command']]
 x['metadata_manifest']=x['metadata_manifest'].replace('/codex-cx-tx2-decoders2-20261107/','/codex-cx-tx2-decoders3-20261107/')
 x['env'].update(TMPDIR=B+'/NJY_tmp',CARGO_TARGET_DIR=B+'/NJY_target',CARGO_NET_OFFLINE='true')
 g=files.pop('NIJ_gate.py');marker="(B/(a+'-graph-check.json')).write_text"
 g=g.replace(marker,"out['all_features']=[dict(name=p['name'],version=p['version'],source=p.get('source'),features=nodes[p['id']]['features']) for p in sorted(m['packages'],key=lambda p:(p['name'],p['version'],p['id']))]\n"+marker)
 files['NJY_gate.py']=g
 return x,files

def submit(a,target,parent,module,text,mode='positive',edits=None):
 assert a.startswith('NJY_K') and 1<=int(a[-3:])<=90 and not (E/a).exists()
 x,files=baseline();key='NIJ_src/'+parent
 files[key]+='\n#[cfg(kani)]\n#[path="'+module+'.rs"]\nmod '+module+';\n'
 files['NIJ_src/'+str(Path(parent).parent/(module+'.rs'))]=text
 files['NIJ_erasure.py']=files['NIJ_erasure.py'].replace("for module in [","for module in ['"+module+"',")
 if edits:
  for old,new in edits:
   assert files[key].count(old)==1;files[key]=files[key].replace(old,new)
  # Exact source erasure of authored instrumentation, before inherited validation.
  files['NIJ_erasure.py']=files['NIJ_erasure.py'].replace('def erase(n,s,zero):','def erase(n,s,zero):\n for old,new in '+repr(edits)+':\n  if new in s:s=s.replace(new,old,1)')
 pins=json.loads(files['NIJ_SOURCE_PINS.json'])
 for n,t in files.items():
  if n.startswith('NIJ_src/') and not n.endswith('Cargo.lock'):pins[n[8:]]=sha(t.encode())
 files['NIJ_SOURCE_PINS.json']=json.dumps(pins)
 x['native_command'][x['native_command'].index('--harness')+1]=target
 x.update(attempt=a,module=target,command=['python3','NJY_gate.py',a+'.json'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,expected_time='optimized compilation, then '+target,control=mode)
 for k in ['historical_gate_command','original_attempt','original_config_file','original_config_sha256','old_target']:x.pop(k,None)
 if mode=='inverse':x['env']['RUSTFLAGS']+=' --cfg NJY_invert'
 x['sources']=list(files);x['deps_fingerprint']={'selected_objects':{}}
 files[a+'.json']=json.dumps(x,indent=1)+'\n';(E/(a+'.json')).write_text(files[a+'.json'])
 idx=json.loads((E/'NJY_INPUTS.json').read_text());idx['attempts'][a]={}
 for n,t in files.items():
  raw=t.encode();h=sha(raw);p=E/'NJY_INPUTS'/(h+'.xz')
  if not p.exists():p.write_bytes(lzma.compress(raw))
  idx['objects'][h]=dict(path=str(p.relative_to(E)),bytes=len(raw),archive_sha256=sha(p.read_bytes()));idx['attempts'][a][n]=h
 (E/'NJY_INPUTS.json').write_text(json.dumps(idx,indent=1)+'\n')
 admission(a)
 payload=base64.b64encode(lzma.compress(json.dumps(files).encode())).decode()
 r=ssh('python3',f'''from pathlib import Path
import json,lzma,base64
b=Path({B!r});files=json.loads(lzma.decompress(base64.b64decode({payload!r})))
for n,t in files.items():
 p=b/n;assert p.resolve().is_relative_to(b.resolve());p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
''');assert r.returncode==0,r.stderr
 r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
 (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
 r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});a={a!r};paths=[p for p in (b/a).rglob('*') if p.is_file() and 'sources' not in p.relative_to(b/a).parts]
paths += [p for pat in ['-graph*','-source*','-lock*','-erasure*'] for p in b.glob(a+pat)]
print(json.dumps({{str(p.relative_to(b)):p.read_text() for p in paths}}))
''');assert r.returncode==0,r.stderr
 out=json.loads(r.stdout)
 for n,t in out.items():
  p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
  if n.endswith('.log'):
   p.with_name(p.name+'.xz').write_bytes(lzma.compress(t.encode()));p.with_name(p.name+'.sha256').write_text(sha(t.encode())+'\n')
  else:p.write_text(t)
 rc=json.loads(out[a+'/receipt.json'])
 with (E/'NJY_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
 print(json.dumps({k:rc[k] for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps']}),flush=True)
 return rc
