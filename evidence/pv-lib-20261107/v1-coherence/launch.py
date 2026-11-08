"""Serial turn/admission/capped launcher for v1 dependency-ordered batches.
Range extension: 565xx only; 558xx/561xx/563xx remain untouched.
"""
import pathlib,json,subprocess,sys,time,shlex
E=pathlib.Path('evidence/pv-lib-20261107/v1-coherence');V='/home/dombarker/project-offloads/codex-pv-lib-slice-20261107/v1-coherence';host='dombarker@100.108.41.90'
a=int(sys.argv[1]);assert 56500<=a<=56589;assert not (E/f'turn-{a}.json').exists()
t=time.time();cmd=['ssh',host,'STREAMB_SLOTS=3 /home/dombarker/streamb-slots/turn.sh'];r=subprocess.run(cmd,text=True,capture_output=True);turn=dict(attempt=a,command=cmd,exit=r.returncode,wall=time.time()-t,stdout=r.stdout,stderr=r.stderr);(E/f'turn-{a}.json').write_text(json.dumps(turn,indent=2));assert r.returncode==0
code=r'''
import json,sys,pathlib,subprocess,os,re,time
x=json.load(sys.stdin);a=x['attempt'];V=pathlib.Path('HOST');E=V/'evidence'
assert 56500<=a<=56589 and not (E/f'batch-{a}.json').exists()
pat=re.compile(r'(^|[-_])'+str(a)+r'([-_.]|$)');hits=[]
for p in V.parents[1].glob('codex-*'):
 for d,dirs,files in os.walk(p/'evidence'):
  hits += [os.path.join(d,n) for n in files if pat.search(n)]
assert not hits,hits
(E/f'id-audit-{a}.json').write_text(json.dumps(dict(attempt=a,hits=hits)))
subprocess.run(['python3',str(V/'reuse.py')],check=True)
plan=json.load(open(V/'PLAN.json'));done={p.name.removesuffix('.olean') for p in (V/'objects-resolved').glob('*.olean')}
remaining=[m for m in plan['order'] if m not in done];batch=remaining[:20]
if not batch:print('ALL_PLANNED_MODULES_COMPILED');sys.exit(3)
(E/f'batch-{a}.json').write_text(json.dumps(batch));(E/f'turn-{a}.json').write_text(json.dumps(x['turn']))
(V/'batch.py').write_text(x['script'])
scanner='/home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py'
with (E/f'admission-{a}.log').open('w') as f:r=subprocess.run(['python3',scanner,str(E/f'admission-{a}.json')],stdout=f,stderr=subprocess.STDOUT)
admit=json.load(open(E/f'admission-{a}.json'))
if r.returncode or admit.get('allowed') is not True:
 (E/f'receipt-{a}.json').write_text(json.dumps(dict(exit=r.returncode,accepted=False,refusal=True,epoch=time.time())));sys.exit(78)
cmd=['systemd-run','--user','--scope','--quiet',f'--unit=pv-lib-{a}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',str(E/f'time-{a}.log'),'python3',str(V/'batch.py'),str(a)]
with (E/f'out-{a}.log').open('w') as f:
 r=subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,cwd=V,text=True)
 for line in r.stdout:
  f.write(line);f.flush();print(line,end='',flush=True)
 r.wait()
(E/f'receipt-{a}.json').write_text(json.dumps(dict(attempt=a,targets=batch,source_revision=plan['revision'],exit=r.returncode,accepted=r.returncode==0,command=cmd)))
sys.exit(r.returncode)
'''.replace('HOST',V)
r=subprocess.Popen(['ssh',host,'python3 -c '+shlex.quote(code)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
r.stdin.write(json.dumps(dict(attempt=a,turn=turn,script=(E/'batch.py').read_text())));r.stdin.close()
lines=[]
for line in r.stdout:
    lines.append(line);print(line,end='',flush=True)
r.wait()
(E/f'transport-{a}.json').write_text(json.dumps(dict(exit=r.returncode,stdout=''.join(lines),stderr=''),indent=2));sys.exit(r.returncode)
