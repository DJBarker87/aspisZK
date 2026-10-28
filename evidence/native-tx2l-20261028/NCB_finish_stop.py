from pathlib import Path
import subprocess,shlex,json,time
E=Path(__file__).resolve().parent
expected=json.loads((E/'NCB_K055-source-check.json').read_text())['after']
code='''from pathlib import Path
import hashlib,json,shutil,os
b=Path('/home/dombarker/project-offloads/codex-cx-native-tx2l-20261028');s=b/'NCB_src'
expected=json.loads(EXPECTED)
errors=[{'path':n,'expected':h,'actual':hashlib.sha256((s/n).read_bytes()).hexdigest() if (s/n).is_file() else None} for n,h in expected.items() if not (s/n).is_file() or hashlib.sha256((s/n).read_bytes()).hexdigest()!=h]
active=[]
for proc in Path('/proc').iterdir():
 if proc.name.isdigit():
  try:
   argv=(proc/'cmdline').read_bytes().split(b'\\0')
   if len(argv)>2 and Path(argv[1].decode()).name in ['S2W_run_host.py','S2W_lean_host.py'] and argv[2].startswith(b'NCB_') and (proc/'cwd').resolve()==b:active.append({'pid':proc.name,'argv':[a.decode() for a in argv if a]})
  except (OSError,UnicodeDecodeError):pass
assert not active,active
cache=Path('/home/dombarker/project-offloads/codex-cx-tx2mid-cache-20261028')
pins={str(p.relative_to(cache)):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in cache.rglob('*') if p.is_file()}
library=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects')
paths=[library/'Aeneas.olean']+list((library/'Aeneas').rglob('*.olean'))
libs={str(p):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in paths}
removed=[]
for name in ['NCB_target','NCB_tmp','.lake']:
 p=b/name
 if p.exists():
  assert not p.is_symlink(),str(p)
  size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file());shutil.rmtree(p);removed.append({'path':str(p),'bytes':size})
print(json.dumps({'source':{'checked':len(expected),'errors':errors,'lock_sha256':hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest()},'owned_active_scopes':active,'cache':pins,'library':libs,'removed':removed,'persistent_cache_retained':str(cache),'scratch_retained':str(s.resolve())}))
'''.replace('EXPECTED',repr(json.dumps(expected)))
for trial in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2','dombarker@100.108.41.90','python3'],capture_output=True,text=True,input=code)
 with (E/'NCB_END_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps({'trial':trial,'exit':r.returncode,'stderr':r.stderr,'stdout_sha256':__import__('hashlib').sha256(r.stdout.encode()).hexdigest()})+'\n')
 if r.returncode==255 and trial<10:time.sleep(60);continue
 assert r.returncode==0,r.stdout+r.stderr
 x=json.loads(r.stdout);(E/'NCB_END.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({'source':x['source'],'owned_active_scopes':x['owned_active_scopes'],'removed':x['removed']}));break
else:raise SystemExit('read-only recovery exhausted; do not launch proofs')
