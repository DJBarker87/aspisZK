from pathlib import Path
import json,subprocess,time,os,sys,hashlib,re
# Invoked only by the lead's future admitted agg16 scope. Never admits or launches.
assert len(sys.argv)==3, 'usage: AGG-SEQUENCE.py <fresh-output-directory> <source-revision>'
D=Path(__file__).resolve().parent
P=D.parent/'codex-pv-evhc8-20261104'
E=Path(sys.argv[1]).resolve();E.mkdir(exist_ok=False)
for n in ['PV_BR_FixtureConsumer.lean','PV_NER_Scan.lean','COMBINED-MANIFEST.jsonl','SCAN-ROOTS.json','EXPECTED-SCAN-MODULES.json','RAW-ROOTS.json','ALL-OBJECT-HASH-CHECKS.json','lakefile.toml','lake-manifest.json','lean-toolchain']:
 (E/n).write_bytes((P/n).read_bytes())
(E/'inputs').mkdir();(E/'inputs/NER_AXIOMS.json').write_bytes((P/'inputs/NER_AXIOMS.json').read_bytes())
os.chdir(E)
def read(n):return json.loads(Path(n).read_text())
def save(n,v):Path(n).write_text(json.dumps(v,indent=2)+'\n')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
L='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake'
O='/home/dombarker/project-offloads/codex-pv-evhc6-20261103/objects'
base=[L,'env','lean','-j1','-M15000','-DElab.async=false']
steps=[]
def stop(reason):
 save('SEQUENCE.json',dict(status='FAIL',reason=reason,steps=steps,composition_counts=False,source_revision=sys.argv[2]))
 print('SEQUENCE STOP',reason,flush=True);sys.exit(1)
def run(i,target,cmd):
 row=dict(step=i,target=target,command=cmd,source_revision=sys.argv[2]);steps.append(row)
 print('START STEP',i,target,flush=True);start=time.monotonic()
 with open(f'step-{i}.log','w') as log:
  p=subprocess.run(['/usr/bin/time','-v','-o',f'step-{i}-time.log','timeout','600',*cmd],stdout=log,stderr=subprocess.STDOUT)
 row.update(exit_status=p.returncode,wall_seconds=time.monotonic()-start)
 tim=Path(f'step-{i}-time.log').read_text()
 for key,label in [('peak_rss_kib','Maximum resident set size'),('swaps','Swaps')]:row[key]=next((l.split(':',1)[1].strip() for l in tim.splitlines() if label in l),None)
 log=Path(f'step-{i}.log').read_text();row['print_axioms']=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log)
 print(log,flush=True);save(f'step-{i}.json',row)
 if p.returncode:stop(f'step {i} exited {p.returncode}; no retry')
 return row
try:
 # Recheck all admitted pins inside the same scope, before the compiler starts.
 for row in read('ALL-OBJECT-HASH-CHECKS.json'):assert sha(row['path'])==row['sha256'],row['path']
 run(1,'PV_BR_FixtureConsumer',base+['-o',O+'/PV_BR_FixtureConsumer.olean','PV_BR_FixtureConsumer.lean'])
 artifacts=[]
 for f in [Path(O+'/PV_BR_FixtureConsumer.olean'),Path(O+'/PV_BR_FixtureConsumer.olean.server'),Path(O+'/PV_BR_FixtureConsumer.olean.private'),Path(O+'/PV_BR_FixtureConsumer.ir')]:
  if f.exists():artifacts.append(dict(path=str(f),sha256=sha(f),bytes=f.stat().st_size))
 save('CONSUMER-OBJECT-PINS.json',artifacts)
 run(2,'NER_SCAN full combined import closure',base+['--run','PV_NER_Scan.lean'])
 rows=list(map(json.loads,Path('COMBINED-SCAN-ROWS.jsonl').read_text().splitlines()))
 assert {r['module'] for r in rows}==set(read('EXPECTED-SCAN-MODULES.json'))
 assert len(rows)==len({r['module'] for r in rows})
 scan=dict(status='coherent',module_count=len(rows),dangling_references=sum(len(r['dangling']) for r in rows),imports_all_match=all(r['imports_match'] for r in rows),declarations=sum(r['declarations'] for r in rows),edges=sum(r['edges'] for r in rows),rows_sha256=sha('COMBINED-SCAN-ROWS.jsonl'),full_rows='COMBINED-SCAN-ROWS.jsonl',consumer_included=True,both_soundness_branches_included=True)
 save('SCAN.json',scan)
 assert scan['dangling_references']==0 and scan['imports_all_match'],scan
 run(3,'NEP raw walk: all consumer roots and both soundness roots',base+['--run',str(D/'NEP_Driver.lean'),'final'])
 log=Path('step-3.log').read_text();results=[json.loads(s) for s in re.findall(r'NEP_RESULT (\{[^\n]+\})',log)]
 assert len(results)==len(read('RAW-ROOTS.json')) and {r['root'] for r in results}==set(read('RAW-ROOTS.json'))
 standard=['Classical.choice','Quot.sound','propext']
 assert all(r['equal'] and r['walked_axioms']==r['collect_axioms'] and set(r['walked_axioms'])<=set(standard) for r in results)
 expected={r['root']:r for r in read('inputs/NER_AXIOMS.json')['roots']}
 for r in results:
  if r['root'] in expected:
   p=expected[r['root']]
   for k in ['reachable_constants','edges_scanned','walked_axioms','collect_axioms','equal']:assert r[k]==p[k],(r,p)
 save('RAW-AXIOMS.json',dict(status='PASS',roots=results,complete=True,soundness_matches_NER_AXIOMS=True,print_axioms=steps[-1]['print_axioms']))
 save('SEQUENCE.json',dict(status='PASS',steps=steps,composition_counts=True,source_revision=sys.argv[2]))
 print('ALL THREE PASS',flush=True)
except BaseException as exc:
 if isinstance(exc,SystemExit):raise
 stop(repr(exc))
