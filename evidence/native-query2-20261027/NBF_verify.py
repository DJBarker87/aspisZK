from pathlib import Path
import json,hashlib,re,subprocess,ast,time,resource,platform,datetime
from NBF_payloads import read_payload
started=time.monotonic()
E=Path(__file__).resolve().parent;root=Path.cwd()
rows=[];errors=[]
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
redundant={'NBF_L027'}
transport=[]
for name in ['NBF_STEP_TRANSPORT.jsonl','NBF_NATIVE_TRANSPORT.jsonl']:
 for line in (E/name).read_text().splitlines():transport.append(json.loads(line))
for p in sorted(E.glob('NBF_[LKG]*/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];kind=r['kind'];log=(p.parent/'stdout.log').read_text()
 if r['limits']!=limits:errors.append([a,'caps'])
 ad=json.loads((E/(a+'-reservation.json')).read_text())
 if ad.get('allowed') is not True:errors.append([a,'admission JSON'])
 admitted=[x for x in transport if x.get('exit')==0 and 'S2H_reservation.py' in str(x.get('command',x.get('argv',''))) and a+'-reservation.json' in str(x.get('command',x.get('argv',''))) and '"allowed": true' in x.get('stdout','')]
 if not admitted:errors.append([a,'no exit0+allowed true transport receipt'])
 for n,h in r['source_hashes'].items():
  q=p.parent/'sources'/n
  if kind=='lean' and (not q.is_file() or hashlib.sha256(q.read_bytes()).hexdigest()!=h):errors.append([a,n,'source snapshot'])
 if kind=='lean' and '-M7000' not in r['command']:errors.append([a,'Lean M cap'])
 if kind=='kani':
  metadata=json.loads((E/a.replace('_K','_G')/'receipt.json').read_text())
  if metadata['source_hashes']!=r['source_hashes']:errors.append([a,'graph/source drift'])
  g=json.loads((E/(a+'-graph-check.json')).read_text())
  if not g['exact_frozen_resolved_graph_match'] or not g['lock_unchanged'] or g['lock_before_sha256']!=g['lock_after_sha256']:errors.append([a,'graph/lock'])
  if r['env']['CARGO_NET_OFFLINE']!='true' or r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']!='3':errors.append([a,'offline/optimized'])
  if '--locked' in r['command']:errors.append([a,'Kani unsupported flag'])
  if not (p.parent/'NBF_harness.patch').is_file():errors.append([a,'missing historical patch'])
 if kind=='lean' and r['exit_status']==0:
  for line in r['print_axioms']:
   m=re.search(r'axioms: \[([^\]]*)\]',line)
   if m and set(m.group(1).split(', '))-{'propext','Classical.choice','Quot.sound'}:errors.append([a,'axioms',line])
 rows.append({k:r[k] for k in ['attempt','kind','source_revision','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}|{'credited':r['exit_status']==0 and a not in redundant,'timed_out':'CBMC timed out' in log or r['exit_status']==124,'memory_rejected':'excessive memory consumption' in log,'redundant':a in redundant})
lean=[r for r in rows if r['kind']=='lean'];kani=[r for r in rows if r['kind']=='kani'];meta=[r for r in rows if r['kind']=='metadata']
audit=json.loads((E/'NBF_L046/receipt.json').read_text());assert audit['exit_status']==0
names=json.loads((E/'NBF_THEOREMS.json').read_text());seen=[re.search("'([^']+)'",x).group(1) for x in audit['print_axioms']]
if sorted(names)!=sorted(seen):errors.append('final audit coverage')
for p in E.glob('NBF_*.lean'):
 s=p.read_text()
 if re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\b|set_option\s+(maxRecDepth|maxHeartbeats)|^import\s+XRn',s,re.M):errors.append([p.name,'forbidden Lean source'])
 accepted=[r for r in lean if r['exit_status']==0 and any(n.endswith('/'+p.name) for n in r['source_hashes'])]
 if not any(hashlib.sha256(p.read_bytes()).hexdigest() in r['source_hashes'].values() for r in accepted):errors.append([p.name,'no accepted exact source'])
 copy=root/'docs/research/100bit-spend-path-20261013/lean'/p.name
 if not copy.is_file() or copy.read_bytes()!=p.read_bytes():errors.append([p.name,'installed source differs'])
for p in E.glob('*.py'):ast.parse(p.read_text())
base='9634aae1cd4f75441a66575baddb50c9c5798e77'
changed=subprocess.check_output(['git','diff','--name-only',base,'--'],text=True).splitlines()
for n in changed:
 if not (n.startswith('evidence/native-query2-20261027/') or n.startswith('docs/research/100bit-spend-path-20261013/lean/NBF_')):errors.append(['outside assigned prefix',n])
tracked=subprocess.check_output(['git','ls-files','evidence/native-query2-20261027','docs/research/100bit-spend-path-20261013/lean/NBF_*'],text=True).splitlines()
if any(Path(n).suffix in ['.pyc','.olean','.o','.a','.so','.elf'] for n in tracked):errors.append('tracked binary')
cleanup=json.loads((E/'NBF_CLEANUP_FINDING.json').read_text())
assert cleanup['summary']['rust_target_absent'] and cleanup['persistent_cache_retained']
assert not cleanup['initial_objects_missing']
assert all(not row['directly_selected_by_passed_NBF_compiles'] for row in cleanup['changes'])
deps=json.loads((E/'NBF_SELECTED_DEPENDENCIES.json').read_text());assert not deps['errors']
terminal=json.loads((E/'NBF_TERMINAL_SOURCE.json').read_text())
for name in ['NBF_harness.rs','NBF_query.rs']:
 actual=hashlib.sha256(read_payload(name).encode()).hexdigest()
 if actual!=terminal['source_hashes']['crates/aspis-r1-cost-probe/src/'+name]['sha256']:errors.append([name,'final patch payload hash'])

if terminal['errors'] or terminal['live_provers'] or not terminal['local_frozen_release_unchanged']:errors.append('terminal source/prover inventory')
archive=json.loads((E/'NBF_ARCHIVE.json').read_text())
for r in kani:
 if r['attempt'] not in archive:errors.append([r['attempt'],'archive missing'])
 if {n:v['sha256'] for n,v in archive.get(r['attempt'],{}).items()}!=r['source_hashes']:errors.append([r['attempt'],'archive hashes'])
def summary(rs):return dict(attempts=len(rs),passes=sum(r['exit_status']==0 for r in rs),failures=sum(r['exit_status']!=0 for r in rs),redundant=sum(r['redundant'] for r in rs),wall_seconds=sum(r['wall_seconds'] for r in rs),peak_rss_kib=max(int(r['peak_rss_kib']) for r in rs),swaps=sum(int(r['swaps']) for r in rs))
assert len(lean)<=100 and len(kani)<=30
out=dict(status='OPEN',validation_status='FINDINGS_RETAINED',worker_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',global_cache_unchanged=cleanup['global_cache_unchanged'],cache_drift=cleanup['changes'],direct_selected_dependencies_unchanged=not deps['errors'],headline='AspisR1.RPx_Deployed.deployed',headline_premises_removed=0,L154='statement parameter',trust='narrowed D188 unchanged',lean=summary(lean),kani=summary(kani),metadata=summary(meta),budgets=dict(lean_max=100,kani_max=30,kani_exhausted=len(kani)==30),final_audit='NBF_L046',public_theorems=len(names),errors=errors,recorded_deviations=['one redundant L027 compile','read-only SSH overlap recorded in NBF_TRANSPORT_NOTE.md'],attempts=rows)
out['static_validation']=dict(target='NBF receipt/source/domain audit',exit_status=int(bool(errors)),wall_seconds=time.monotonic()-started,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/(1024 if platform.system()=='Darwin' else 1),swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),axioms='N/A: read-only Python audit; exact formal prints in NBF_L046',at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(E/'NBF_VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n')
(E/'NBF_attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
assert not errors,errors
print(json.dumps({k:out[k] for k in ['status','lean','kani','metadata','public_theorems','errors']}))
