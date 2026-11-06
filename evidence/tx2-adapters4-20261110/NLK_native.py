"""Owned runner: frozen offline graph, exact KMX, source erasure, isolated target."""
from NLK_transport import *
from NLK_inspect import inputs,read
import hashlib,lzma,base64,shlex
sha=lambda b:hashlib.sha256(b).hexdigest()
def baseline():
 files=inputs();x=json.loads(read('evidence/slice-d-entry8-20261107/NJD_K001.json'))
 for n in list(files):
  if n.startswith('NJD_'):files.pop(n)
 # Keep only immutable historical inputs; restore every reached frozen parent.
 for parent in ['programs/r1-cost-probe/src/r1_pool_adapter.rs','programs/r1-cost-probe/src/r1_pool_adapter_owned.rs','programs/r1-cost-probe/src/lib.rs','crates/aspis-statement/src/lib.rs','crates/aspis-statement/src/pool_v1/verifier_registry.rs']:
  files['NLK_src/'+parent]=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+parent],text=True)
 for parent in ['programs/r1-cost-probe/src/lib.rs','crates/aspis-statement/src/lib.rs']:
  files['NLK_src/'+parent]='#![cfg_attr(kani,feature(allocator_api))]\n'+files['NLK_src/'+parent]
 files={k.replace('NIJ_src/','NLK_src/'):v for k,v in files.items()}
 x['native_command']=[v.replace('/codex-cx-slice-d-entry8-20261107/','/codex-cx-tx2-adapters4-20261110/').replace('/NIJ_src/','/NLK_src/').replace('/NJD_target','/NLK_target') for v in x['native_command']]
 x['metadata_manifest']=B+'/NLK_src/programs/r1-cost-probe/Cargo.toml'
 x['env']['RUSTFLAGS']+=' -C opt-level=3'
 x['env'].update(TMPDIR=B+'/NLK_tmp',CARGO_TARGET_DIR=B+'/NLK_target',CARGO_NET_OFFLINE='true')
 gate=files.pop('NIJ_gate.py').replace("B/'NIJ_src'","B/'NLK_src'")
 marker="(B/(a+'-graph-check.json')).write_text"
 gate=gate.replace(marker,"out['all_features']=[dict(name=p['name'],version=p['version'],source=p.get('source'),features=nodes[p['id']]['features']) for p in sorted(m['packages'],key=lambda p:(p['name'],p['version'],p['id']))]\n"+marker)
 files['NLK_gate.py']=gate
 return x,files

def submit(a,target,parent,module,text,mode='positive',edits=None,extra_sidecars=None):
 assert a.startswith('NLK_K') and 1<=int(a[-3:]) and not (E/a).exists()
 used=[json.loads(line) for line in (E/'NLK_ATTEMPTS.jsonl').read_text().splitlines() if json.loads(line).get('kind')=='kani']
 assert len(used)<60,'Kani invocation budget exhausted; all receipt-bearing attempts count except verified prelaunch K001'
 x,files=baseline();key='NLK_src/'+parent
 files[key]+='\n#[cfg(kani)]\n#[path="'+module+'.rs"]\nmod '+module+';\n'
 files['NLK_src/'+str(Path(parent).parent/(module+'.rs'))]=text
 files['NIJ_erasure.py']=files['NIJ_erasure.py'].replace("for module in [","for module in ['"+module+"',")
 for extra_parent,extra_module,extra_text in (extra_sidecars or []):
  extra_raw=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+extra_parent],text=True)
  frozen_pins=json.loads(files['NGL_FROZEN_SOURCE_PINS.json']);assert sha(extra_raw.encode())==frozen_pins[extra_parent]
  visibility='pub(crate) ' if a=='NLK_K081' and extra_module=='NLK_pda' else ''
  files['NLK_src/'+extra_parent]=extra_raw+'\n#[cfg(kani)]\n#[path="'+extra_module+'.rs"]\n'+visibility+'mod '+extra_module+';\n'
  if visibility:
   files['NIJ_erasure.py']=files['NIJ_erasure.py'].replace('if s.endswith(suffix):s=s[:-len(suffix)]',"public=suffix.replace('mod '+module,'pub(crate) mod '+module)\n  if s.endswith(public):s=s[:-len(public)]\n  if s.endswith(suffix):s=s[:-len(suffix)]")
  files['NLK_src/'+str(Path(extra_parent).parent/(extra_module+'.rs'))]=extra_text
  files['NIJ_erasure.py']=files['NIJ_erasure.py'].replace("for module in [","for module in ['"+extra_module+"',")
 if edits:
  for old,new in edits:
   assert files[key].count(old)==1;files[key]=files[key].replace(old,new)
  # Exact source erasure of authored instrumentation, before inherited validation.
  files['NIJ_erasure.py']=files['NIJ_erasure.py'].replace('def erase(n,s,zero):','def erase(n,s,zero):\n for old,new in '+repr(edits)+':\n  if new in s:s=s.replace(new,old,1)')
 pins=json.loads(files['NIJ_SOURCE_PINS.json']);pins.update(json.loads(files['NGL_FROZEN_SOURCE_PINS.json']));pins.pop('programs/r1-cost-probe/src/NJD_stages.rs',None)
 for n,t in files.items():
  if n.startswith('NLK_src/') and not n.endswith('Cargo.lock'):pins[n[8:]]=sha(t.encode())
 files['NIJ_SOURCE_PINS.json']=json.dumps(pins)
 x['native_command'][x['native_command'].index('--harness')+1]=target
 x.update(attempt=a,module=target,command=['python3','NLK_gate.py',a+'.json'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,expected_time='optimized compilation, then '+target,control=mode)
 for k in ['historical_gate_command','original_attempt','original_config_file','original_config_sha256','old_target']:x.pop(k,None)
 x['sources']=list(files);x['deps_fingerprint']={'selected_objects':{}}
 files[a+'.json']=json.dumps(x,indent=1)+'\n';(E/(a+'.json')).write_text(files[a+'.json'])
 idx=json.loads((E/'NLK_INPUTS.json').read_text());idx['attempts'][a]={}
 for n,t in files.items():
  raw=t.encode();h=sha(raw);p=E/'NLK_INPUTS'/(h+'.xz')
  if not p.exists():p.write_bytes(lzma.compress(raw))
  idx['objects'][h]=dict(path=str(p.relative_to(E)),bytes=len(raw),archive_sha256=sha(p.read_bytes()));idx['attempts'][a][n]=h
 (E/'NLK_INPUTS.json').write_text(json.dumps(idx,indent=1)+'\n')
 admission(a)
 payload=base64.b64encode(lzma.compress(json.dumps(files).encode())).decode()
 r=ssh('python3',f'''from pathlib import Path
import json,lzma,base64
b=Path({B!r});files=json.loads(lzma.decompress(base64.b64decode({payload!r})))
for n,t in files.items():
 p=b/n;assert p.resolve().is_relative_to(b.resolve());p.parent.mkdir(parents=True,exist_ok=True)
 if not p.exists() or p.read_text()!=t:p.write_text(t)
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
 with (E/'NLK_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
 print(json.dumps({k:rc[k] for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps']}),flush=True)
 return rc
