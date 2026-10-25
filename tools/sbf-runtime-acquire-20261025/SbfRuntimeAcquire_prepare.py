"""Immutable data copy and pure AST/byte preflight; never execute payload."""
import ast, hashlib, json, pathlib, resource, subprocess, sys, time
START=time.monotonic()
ROOT=pathlib.Path(__file__).resolve().parents[2]
HERE=ROOT/'tools/sbf-runtime-acquire-20261025'
OUT=ROOT/'evidence/sbf-runtime-acquire-20261025'
def pin(b):return dict(size=len(b),sha256=hashlib.sha256(b).hexdigest())
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def save(name,obj):
 b=(json.dumps(obj,indent=2,sort_keys=True)+'\n').encode();assert len(b)<=5_000_000;(OUT/name).write_bytes(b)
def blob(rev,path):return git('show',rev+':'+path)
assert git('branch','--show-current').decode().strip()=='codex/cx-sbf-runtime-acquire-20261025'
index={}
for folder in ('tools','evidence'):
 prefix=folder+'/sbf-runtime-finish-20261025/'
 for path in git('ls-tree','-r','--name-only','9e48b23c90',prefix).decode().splitlines():
  b=blob('9e48b23c90',path)
  name='SbfRuntimeAcquire-source-'+path.rsplit('/',1)[1]
  dest=(HERE if folder=='tools' else OUT)/name
  dest.write_bytes(b)
  index['9e48b23c90:'+path]=dict(copy=str(dest.relative_to(ROOT)),**pin(b))
  if path.endswith(('.py','.py.txt')):ast.parse(b)
  elif path.endswith('.json'):json.loads(b)
def source(name):return blob('9e48b23c90','tools/sbf-runtime-finish-20261025/SbfRuntimeFinish'+name)
payload=source('_payload.py.txt');planraw=blob('9e48b23c90','evidence/sbf-runtime-finish-20261025/SbfRuntimeFinish-plan.json');plan=json.loads(planraw)
assert pin(payload)==dict(size=145492,sha256='4349df520cf0cefa586c997e7c5adf6963d125767ef239364da18bff6eacf8b6')
assert pin(planraw)==dict(size=194656,sha256='4fd92867306a043f35157063e969f3f206656e5effefd9955afbe35e56ced5f6')
guard=blob('13abf7fe51','tools/resource-meta1g-20261025/ResourceMeta1G_guard.py')
elf=blob('2ce034b264','tools/sbf-runtime-trace-20261025/SbfRuntimeTrace-elf.py.txt')
assert guard==source('-guard.py.txt') and elf==source('-elf.py.txt')
literal=payload.split(b'\nSBF_FINISH_PLAN = ',1)[1].split(b'\n',1)[0]
assert ast.literal_eval(literal.decode())==plan
assert payload==guard+b'\n# END EXACT REVIEWED GUARD\n'+source('_core.py')+b'\n'+elf+b'\nSBF_FINISH_PLAN = '+literal+b'\n'+source('_acquire.py.txt')
pt,gt=ast.parse(payload),ast.parse(guard)
assert ast.dump(gt)==ast.dump(ast.Module(body=pt.body[:len(gt.body)],type_ignores=[]))
protected={'BUDGET','INTERVAL','MAX_SAMPLES','MAX_LINEAGE','Guard','GuardError','Proc','inherited_limits','check_limits'}
for n in ast.walk(ast.Module(body=pt.body[len(gt.body):],type_ignores=[])):
 if isinstance(n,(ast.FunctionDef,ast.ClassDef)):assert n.name not in protected
 if isinstance(n,ast.Name) and isinstance(n.ctx,ast.Store):assert n.id not in protected
 # No assignment to imported stdlib objects, including subscript monkeypatches.
 if isinstance(n,(ast.Assign,ast.AnnAssign,ast.AugAssign)):
  targets=n.targets if isinstance(n,ast.Assign) else [n.target]
  for t in targets:
   if isinstance(t,ast.Attribute):assert not (isinstance(t.value,ast.Name) and t.value.id in {'os','resource','signal','time','threading','json','struct','sys','hashlib','stat'})
for n in ast.walk(pt):
 if isinstance(n,ast.Call):
  if isinstance(n.func,ast.Name):assert n.func.id not in {'exec','eval','__import__'}
  if isinstance(n.func,ast.Attribute):assert n.func.attr not in {'Popen','run','call','check_output','system','fork','execve','execv','posix_spawn','setrlimit','prlimit','CDLL','PyDLL','load','loads'}
 if isinstance(n,ast.Import):assert not any(a.name in {'subprocess','ctypes','marshal'} for a in n.names)
assert len(plan['paths'])==98 and len({r['path'] for r in plan['paths']})==98
assert len(plan['module_fields'])==136 and len(plan['modules'])==68
(HERE/'SbfRuntimeAcquire_payload.py.txt').write_bytes(payload)
(OUT/'SbfRuntimeAcquire-plan.json').write_bytes(planraw)
base=blob('2ce034b264','tools/sbf-runtime-trace-20261025/SbfRuntimeTrace_transport.py')
old='/usr/bin/python3 -I -S -B -';new='/usr/bin/env -i HOME=/probe LC_ALL=C PATH=/usr/bin TMPDIR=/tmp /usr/bin/python3 -I -S -B -'
transport=base.replace(b'sbf-runtime-trace-20261025',b'sbf-runtime-acquire-20261025').replace(b'SbfRuntimeTrace',b'SbfRuntimeAcquire').replace(old.encode(),new.encode())
reversed_bytes=transport.replace(new.encode(),old.encode()).replace(b'sbf-runtime-acquire-20261025',b'sbf-runtime-trace-20261025').replace(b'SbfRuntimeAcquire',b'SbfRuntimeTrace')
assert reversed_bytes==base and ast.dump(ast.parse(reversed_bytes))==ast.dump(ast.parse(base))
(HERE/'SbfRuntimeAcquire_transport.py').write_bytes(transport)
tt=ast.parse(transport);assert sum(isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr=='Popen' for n in ast.walk(tt))==1
argv=next(ast.literal_eval(n.value) for n in tt.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='ARGV' for t in n.targets))
assert argv==['ssh','-T','-o','BatchMode=yes','-o','ConnectionAttempts=1','-o','ConnectTimeout=15','dombarker@100.108.41.90',new]
review=pathlib.Path('/private/tmp/lead-sbf-runtime-finish-review-20261025-v1/receipt.json').read_bytes()
(OUT/'SbfRuntimeAcquire-lead-review-receipt.json').write_bytes(review)
assert json.loads(review)['new_tests']==35
save('SbfRuntimeAcquire-immutable-inputs.json',index)
# Exact public API/core and all upstream source/dependency pins retained in copied inventories/receipts.
sources={str(p.relative_to(ROOT)):pin(p.read_bytes()) for p in sorted(HERE.iterdir()) if p.is_file()}
sources[str((OUT/'SbfRuntimeAcquire-plan.json').relative_to(ROOT))]=pin(planraw)
sources[str((OUT/'SbfRuntimeAcquire-immutable-inputs.json').relative_to(ROOT))]=pin((OUT/'SbfRuntimeAcquire-immutable-inputs.json').read_bytes())
record=dict(job='SbfRuntimeAcquire-20261025',source_revision=git('rev-parse','HEAD').decode().strip(),argv=argv,payload=pin(payload),plan=pin(planraw),sources=sources,
 authority='Current manager ONE distinct changed-source metadata finishing acquisition; exactly one SSH, charged marker before Popen, no retry; supersedes only original future cgroup note',
 original_source_only_preregister='SbfRuntimeAcquire-source-SbfRuntimeFinish-preregister.json preserved byte-exact; no historical authority reused',
 guard=dict(pin=pin(guard),revision='13abf7fe51',budget_bytes=512*2**20,interval_seconds=0.02),
 limits=dict(remote_alarm_seconds=115,transport_deadline_seconds=120,output_bytes=4*2**20,connect_seconds=15,attempts=1,file_bytes=16*2**20,unique_bytes=128*2**20,files=512,elf=64,guest_copy_bytes=64*2**20,guest_rows=256,expected_rss_below=128*2**20),
 cgroup_metrics='UNOBSERVED',aggregate_reservations='UNOBSERVED; scan not authorized or needed; no GO/headroom/physical future claim',
 zero_budgets=['tracer','tracee','host Popen','root','sudo','namespace','mount','credential','rlimit setter','native probe','backend','compiler','Lean','Rust','Cargo','Kani','extraction','ELF build','keys','RPC'],
 result_policy='Actual exit retained including78; UNKNOWN/STALE/absence terminal; no JSON invented on error, no second host call; finite INPUT DATA only; runtime approval NULL',
 reused='35 fixtures and review receipts; old205 and RuntimeTrace76+9+116 not rerun; historical evidence not fresh identity',
 elf_pins=dict(default='f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4',devnet='63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299',Pool='121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'),
 inherited_limits='observed by exact remote guard; no setters; postcheck exact equality',axioms='N/A; data')
save('SbfRuntimeAcquire-preregister.json',record)
usage=resource.getrusage(resource.RUSAGE_SELF)
save('SbfRuntimeAcquire-preflight-receipt.json',dict(status='PASS pure AST/byte preflight; payload UNEXECUTED',command=getattr(sys,'orig_argv',sys.argv),source_revision=record['source_revision'],source_overlay=sources,exit=0,wall_seconds=time.monotonic()-START,peak_rss_bytes=usage.ru_maxrss*(1 if sys.platform=='darwin' else 1024),swap=usage.ru_nswap,dependencies={n:dict(path=m.__file__,**pin(pathlib.Path(m.__file__).read_bytes())) for n,m in sorted(sys.modules.items()) if getattr(m,'__file__',None) and pathlib.Path(m.__file__).is_file()},interpreter=dict(path=sys.executable,version=sys.version,**pin(pathlib.Path(sys.executable).read_bytes())),transport_original=pin(base),transport=pin(transport),transport_normalized_byte_identity=True,transport_normalized_AST_identity=True,transport_logic_edits=0,payload=pin(payload),plan=pin(planraw),host_calls=0,fixtures_rerun=0,axioms='N/A; data'))
print(json.dumps(dict(status='PASS',payload=pin(payload),plan=pin(planraw),transport_normalized_identity=True)))
