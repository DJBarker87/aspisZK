#!/usr/bin/env python3
"""PCO spec-driven extraction controller (host side, runs inside an admitted capped scope).

Same pattern as evidence/emission-repro-20261110/NMH_extract.py: the hash-pinned, unchanged NHR_stage.py supplies
stage/validate/extract and every source, lock and tool check; this controller only supplies options() from a spec
and measures each tool invocation. Differences from NMH_extract.py (recorded in PCVR_CLASSIFICATIONS.json):
  * workspace/attempt log names are PCVR_*;
  * the expected cgroup limits are read from the spec (extraction default 3G/4G, NMH used 6G/8G);
  * after extraction every --opaque selector in the spec is checked against the retained Charon declaration
    inventory (NHR_DECLARATIONS.json) and the result is written to PCVR_OPAQUE_CHECK.json (NHR itself only checks
    selectors it can rewrite to the cost-probe crate, so the spec passes opacity=[] to the stager as NMH did);
  * PCVR_<run>_PINS.json is written: tool binary hashes, full commands, frozen tree/lock hashes, output hashes.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import importlib.util,json,hashlib,subprocess,time,os,types,re
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
spec=json.loads((E/(sys.argv[1]+'_spec.json')).read_text());run=spec['run']
AENEAS_SHA={'original':'959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3','extended':'c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'}
assert sha(Path(spec['aeneas_command'][0]).read_bytes())==AENEAS_SHA[spec['aeneas_tool']],'aeneas does not match the tool named in the spec'
p=E/'NHR_stage.py';pin=json.loads((E/'PCVR_STAGER_PIN.json').read_text());assert sha(p.read_bytes())==pin['sha256'],'stager drift'
loader=importlib.util.spec_from_file_location('PCVR_private_NHR_stage',p);m=importlib.util.module_from_spec(loader);loader.loader.exec_module(m)
if spec.get('features_override'):m.FEATURES=spec['features_override']  # PCVR_ change: stager FEATURES global replaced by the client feature set (stager file unchanged, sha pinned)
rel=next(l.split(':',2)[2].strip().lstrip('/') for l in Path('/proc/self/cgroup').read_text().splitlines() if l.startswith('0:'))
cg=Path('/sys/fs/cgroup')/rel
want=spec.get('expected_limits',{'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0','pids.max':'64'})
assert {n:(cg/n).read_text().strip() for n in ('memory.high','memory.max','memory.swap.max','pids.max')}==want,'not the admitted capped scope'
out=E/(run+'_emitted');out.mkdir(exist_ok=True)
m.options=lambda args,workspace,out:dict(charon_command=spec['charon_command'],aeneas_command=spec['aeneas_command'],opacity=spec.get('opacity',[]),root=spec['configuration'].get('roots') or spec['configuration']['start_from'])
original_run=subprocess.run
def measured(cmd,*a,**kw):
 tool=next((k for k in ['charon','aeneas'] if cmd[0]==spec[k+'_command'][0]),None)
 if not tool:return original_run(cmd,*a,**kw)
 entry=dict(attempt=run,tool=tool,command=cmd,started_unix=time.time(),source_revision=m.REV,tool_sha256=sha(Path(cmd[0]).read_bytes()))
 with (E/'PCVR_TOOL_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n');f.flush();os.fsync(f.fileno())
 xe=spec.get('extra_env')
 if tool=='charon' and kw.get('env') is not None:entry['env_effective']={k:kw['env'].get(k) for k in ('RUSTFLAGS','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS')}
 if xe and tool=='charon' and kw.get('env') is not None:
  e2=dict(kw['env'])
  for k,v in xe.items():
   e2[k]=(e2.get(k,'')+' '+v).strip() if k=='RUSTFLAGS' else v
  kw['env']=e2;entry['env_effective']={k:e2.get(k) for k in xe}
 r=original_run(['/usr/bin/time','-v','-o',str(out/(tool+'.time'))]+cmd,*a,**kw)
 entry.update(exit=r.returncode,wall_seconds=time.time()-entry['started_unix'],time_receipt=str(out/(tool+'.time')))
 (out/(tool+'_receipt.json')).write_text(json.dumps(entry,indent=2)+'\n')
 return r
subprocess.run=measured
args=types.SimpleNamespace(function='repro',cargo='/home/dombarker/.cargo/bin/cargo')
error=None
try:status=m.extract(args,E/'PCVR_workspace',out)
except BaseException as e:status=1;error=repr(e)[:2000]
# ---- post-checks and PINS
def opaque_selectors(cmd):
 return [cmd[i+1] for i,x in enumerate(cmd) if x=='--opaque']
check={'run':run,'selectors':[]}
dj=out/'NHR_DECLARATIONS.json'
if dj.exists():
 inv=json.loads(dj.read_text())
 for sel in opaque_selectors(spec['charon_command']):
  parts=sel.split('::');hits=[]
  for f in inv:
   elems=[x['Ident'][0] if 'Ident' in x else '_' for x in f['name']]
   # 'crate' is the extracted package; compare on the tail so the package alias does not matter
   if len(parts)>=2 and len(parts)==len(elems) and all(pp=='_' or pp==ee or (i==0 and pp=='crate') for i,(pp,ee) in enumerate(zip(parts,elems))):hits.append(f)
  check['selectors'].append(dict(selector=sel,matches=len(hits),all_opaque=bool(hits) and all(h['body_kind'] in ('Opaque',['Opaque']) for h in hits)))
(out/'PCVR_OPAQUE_CHECK.json').write_text(json.dumps(check,indent=2)+'\n')
pj=json.loads((out/'NHR_PINS.json').read_text()) if (out/'NHR_PINS.json').exists() else {}
tools={}
for k in ['charon','aeneas']:
 b=Path(spec[k+'_command'][0]);tools[b.name]=sha(b.read_bytes())
for extra in ['charon-driver']:
 q=Path(spec['charon_command'][0]).parent/extra
 if q.exists():tools[extra]=sha(q.read_bytes())
pins=dict(run=run,aeneas_tool=spec['aeneas_tool'],p1g_config=spec.get('p1g'),spec_id=spec.get('spec_id'),frozen_revision=m.REV,frozen_source_tree_git_hash=spec['frozen_source_tree_git_hash'],cargo_lock_sha256_before=pj.get('lock_before'),cargo_lock_sha256_after=pj.get('lock_after'),
 staging_manifest_sha256=pj.get('manifest_sha256'),stager_sha256=pin['sha256'],controller_sha256=sha(Path(__file__).read_bytes()),
 opacity_file='%s_spec.json'%run,opacity_file_sha256=sha((E/(run+'_spec.json')).read_bytes()),tools=tools,charon_command=spec['charon_command'],aeneas_command=spec['aeneas_command'],
 environment=dict(RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_BUILD_JOBS='1',RAYON_NUM_THREADS='1'),extra_env_appended_to_stager_env=spec.get('extra_env'),
 llbc_sha256=pj.get('llbc_sha256'),charon_exit=pj.get('charon_exit'),aeneas_exit=pj.get('aeneas_exit'),exit=pj.get('exit'),
 output_sha256=pj.get('outputs',{}),opaque_check=check,namespace=spec['configuration'].get('namespace'),start_from=spec['configuration'].get('roots') or spec['configuration']['start_from'],features=spec['configuration'].get('features'))
(out/('%s_PINS.json'%run)).write_text(json.dumps(pins,indent=2,sort_keys=True)+'\n')
pins['controller_error']=error
(out/('%s_PINS.json'%run)).write_text(json.dumps(pins,indent=2,sort_keys=True)+'\n')
print(json.dumps(dict(attempt=run,exit=status,error=error)),flush=True)
sys.exit(status)
