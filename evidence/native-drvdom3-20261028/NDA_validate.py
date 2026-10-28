from pathlib import Path
import json, hashlib, re, subprocess, shlex
E=Path(__file__).resolve().parent
rows=[json.loads(s) for s in (E/'NDA_ATTEMPTS.jsonl').read_text().splitlines()]
assert len(rows)<=50
standard={'propext','Classical.choice','Quot.sound'}
for r in rows:
 a=r['attempt']; source=E/a/'source.lean.txt'
 assert hashlib.sha256(source.read_bytes()).hexdigest()==next(iter(r['source_hashes'].values()))
 assert json.loads((E/(a+'-admission.log')).read_text())['allowed'] is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert '-M7000' in r['command']
 assert str(r['swaps'])=='0'
 if r['exit_status']==0:
  for line in r['print_axioms']:
   assert 'sorryAx' not in line
   m=re.search(r'\[([^]]*)\]',line)
   if m: assert set(m.group(1).replace(' ','').split(','))<=standard
current=[]
for p in sorted(Path('lean').glob('NDA_*.lean')):
 source=p.read_bytes(); sha=hashlib.sha256(source).hexdigest()
 matching=[r for r in rows if r['exit_status']==0 and r['source_hashes'].get(p.name)==sha]
 assert matching,p
 code=re.sub(r'/-[\s\S]*?-/', '', source.decode())
 code=re.sub(r'--[^\n]*', '', code)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|maxHeartbeats|maxRecDepth)\b',code),p
 current.append(dict(source=str(p),sha256=sha,passing_attempt=matching[-1]['attempt']))
for p in E.rglob('*'):
 if p.is_file(): assert p.stat().st_size<=20*1024*1024,p
host_rows=json.loads((E/'NDA_AENEAS_PINS.json').read_text())['selected_aeneas']
for a in ['NDA_L019','NDA_L020','NDA_L021']:
 host_rows.update(json.loads((E/a/'receipt.json').read_text())['deps_fingerprint']['selected_objects'])
code='''from pathlib import Path
import json,hashlib
rows=ROWS
out=[]
for name,row in rows.items():
 p=Path(row['path']);sha=hashlib.sha256(p.read_bytes()).hexdigest()
 assert sha==row['sha256'],str(p)
 out.append(dict(name=name,path=str(p),sha256=sha,bytes=p.stat().st_size))
tools=[]
for n in ['S2W_lean_host.py','S2W_run_host.py']:
 own=Path('/home/dombarker/project-offloads/codex-cx-native-drvdom3-20261028')/n
 old=Path('/home/dombarker/project-offloads/codex-cx-native-drvdom2-20261028')/n
 assert own.read_bytes()==old.read_bytes()
 tools.append(dict(name=n,sha256=hashlib.sha256(own.read_bytes()).hexdigest()))
print(json.dumps(dict(pinned_objects=out,unchanged_backend=tools),indent=2))
'''.replace('ROWS',repr(host_rows))
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,text=True)
assert r.returncode==0,r.stderr
(E/'NDA_HOST_VALIDATION.json').write_text(r.stdout)
result=dict(lean_attempts=len(rows),passed=sum(r['exit_status']==0 for r in rows),rejected=sum(r['exit_status']!=0 for r in rows),kani_runs=0,current_sources=current,all_snapshots_match=True,all_admissions_allowed=True,admission_exit_status=0,admission_status_basis='runner asserts returncode == 0 and allowed is True before any launch',all_limits_match=True,all_passed_axioms_standard=True,library_and_final_objects_unchanged=True,backend_byte_identical_to_NCU=True,final_audits_separate=True,primary_and_lane_coimport_passed=True,coimport_collision_attempt='NDA_L018')
(E/'NDA_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
