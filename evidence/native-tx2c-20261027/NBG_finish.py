"""Read-only end pins, then remove only this job's disposable build/solver dirs.

No prover launches, no persistent-cache writes or deletion. Run once after receipts.
"""
from pathlib import Path
import json, hashlib, subprocess, shlex, time, re

E = Path(__file__).resolve().parent
assert len(list(E.glob('NBG_K*/receipt.json'))) == 30, 'wait for final Kani receipt'
receipts = [json.loads(p.read_text()) for p in E.glob('NBG_*/receipt.json')]
scopes = sorted({Path(x['cgroup']).name for x in receipts})
manifest = json.loads((E/'NBG_SCRATCH_MANIFEST.json').read_text())
launchers = json.loads((E/'NBG_LAUNCHER_INPUTS.json').read_text())
tool_pins = json.loads((E.parent/'native-tx2a-20261027/NBC_TOOL_PINS.json').read_text())
code = '''from pathlib import Path
import hashlib,json,subprocess,shutil
B=Path('/home/dombarker/project-offloads/codex-cx-native-tx2c-20261027')
C=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
cache=Path('/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027')
def pin(p):return dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
'''
code += f'manifest={manifest!r}\nlaunchers={launchers!r}\ntool_pins={tool_pins!r}\nscopes={scopes!r}\n'
code += '''
states={}
for scope in scopes:
 r=subprocess.run(['systemctl','--user','show',scope,'-p','ActiveState','-p','SubState'],capture_output=True,text=True)
 states[scope]=dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr)
 assert 'ActiveState=active' not in r.stdout and 'SubState=running' not in r.stdout,(scope,r.stdout)
S=B/'NBG_src';changed={};missing=[]
for n,sha in manifest.items():
 p=S/n
 if not p.is_file():missing.append(n);continue
 actual=pin(p)
 if actual['sha256']!=sha:
  data=p.read_bytes();suffix=b'\\n#[cfg(kani)]\\nmod NBG_runtime;\\n'
  # Only the cfg(kani) module declaration may be appended to a frozen file.
  assert data.endswith(suffix),(n,'unexpected edit')
  assert hashlib.sha256(data[:-len(suffix)]).hexdigest()==sha,(n,'frozen body changed')
  changed[n]=actual
assert not missing,missing
added={str(p.relative_to(S)):pin(p) for p in S.rglob('*') if p.is_file() and str(p.relative_to(S)) not in manifest}
assert len(changed)==6 and len(added)==6,(changed,added)
assert all(n.endswith('/NBG_runtime.rs') for n in added),added
backend={n:pin(B/n) for n in launchers}
assert all((B/n).read_text()==text for n,text in launchers.items()),'launcher drift'
tools={n:pin(Path(n)) for n in tool_pins}
assert tools==tool_pins,'tool drift'
roots=[B/'.lake/build/lib/lean',cache,C/'objects',C,Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
names=set()
for root in roots:
 for p in [root/'Aeneas.olean',*list((root/'Aeneas').rglob('*.olean'))]:
  if p.is_file():names.add(str(p.relative_to(root)))
selected={n:next(root/n for root in roots if (root/n).is_file()) for n in names}
result=dict(cache={str(p):pin(p) for p in cache.rglob('*') if p.is_file()},aeneas={str(p):pin(p) for p in selected.values()},scratch=dict(frozen_files=len(manifest),changed_cfg_only=changed,new_harnesses=added,missing=missing,lock=pin(S/'Cargo.lock')),backend=backend,tools=tools,scope_states=states)
# Exact path guards: these are owned disposable products, never shared caches.
cleanup={}
for name in ['NBG_target','NBG_tmp']:
 p=B/name
 assert p.parent==B and not p.is_symlink() and p.resolve()==B/name
 files=[q for q in p.rglob('*') if q.is_file()] if p.exists() else []
 cleanup[name]=dict(path=str(p),files=len(files),bytes=sum(q.stat().st_size for q in files))
 if p.exists():shutil.rmtree(p)
 cleanup[name]['absent_after']=not p.exists()
result['cleanup']=cleanup
result['persistent_cache_retained']=cache.is_dir()
(B/'NBG_END.json').write_text(json.dumps(result,indent=2)+'\\n')
print(json.dumps(result))
'''
for retry in range(11):
    # Send this own audit script on stdin; the frozen source manifest exceeds
    # the remote shell's single-argument limit. No validation is weakened.
    r = subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90',
                        'python3 -'],input=code,capture_output=True,text=True)
    with (E/'NBG_END_TRANSPORT.jsonl').open('a') as f:
        f.write(json.dumps(dict(retry=retry,exit=r.returncode,stderr=r.stderr))+'\n')
    if r.returncode == 0:
        break
    # A lost connection during cleanup must be recovered read-only, not repeated.
    if r.returncode == 255:
        raise SystemExit('Recover NBG_END.json read-only; do not resubmit cleanup')
    raise SystemExit(r.stderr)
out = json.loads(r.stdout)
for key,name in [('cache','CACHE_END'),('aeneas','LIBRARY_END')]:
    (E/('NBG_'+name+'.json')).write_text(json.dumps(out[key],indent=2)+'\n')
start = json.loads((E/'NBG_CACHE_START.json').read_text())
out['cache_start_preserved'] = all(out['cache'].get(n)==v for n,v in start.items())
out['aeneas_start_unchanged'] = out['aeneas']==json.loads((E/'NBG_LIBRARY_START.json').read_text())
(E/'NBG_END.json').write_text(json.dumps(out,indent=2)+'\n')
assert out['cache_start_preserved'] and out['aeneas_start_unchanged'], 'pin change: inspect'
print(json.dumps({k:v for k,v in out.items() if k not in ['cache','aeneas','scope_states']},indent=2))
