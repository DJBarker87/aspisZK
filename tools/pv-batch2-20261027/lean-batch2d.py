from pathlib import Path
import hashlib,json,re,shlex,subprocess,sys,time,datetime
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-batch2-20261027/batch2d';D='/home/dombarker/project-offloads/codex-pv-batch2-20261027';H='dombarker@100.108.41.90'
n=int(sys.argv[1]);module=sys.argv[2];assert 39800<=n<=39899
if (E/'HOST-BARRIER-STOP.json').exists():raise SystemExit('STOP: recorded fatal host barrier error; lead repair required before any further compile')
# Refuse locally before consuming an ID if the most recent host hold is young.
for hold in list(E.glob('*-reservation.log'))+list(E.glob('*-admission-barrier.json')):
 try:
  hr=json.loads(hold.read_text())
  if hr.get('allowed') is False:
   until=datetime.datetime.fromisoformat(hr['utc']).timestamp()+180
   assert time.time()>=until, 'cooldown active until '+str(until)
 except (ValueError,KeyError):pass
h5=json.loads((E/'H5-SOURCE-PINS.json').read_text()).get(module)
if h5:
 p=R/h5['path'];assert hashlib.sha256(subprocess.check_output(['git','show','HEAD:'+h5['path']])).hexdigest()==h5['sha256'];assert hashlib.sha256(p.read_bytes()).hexdigest()==h5['sha256']
else:
 p=R/'docs/research/v8-r0-zk-20261009/lean'/(module+'.lean');assert p.name.startswith('PV_B2_')
tp=E/'TALLY.json';t=json.loads(tp.read_text());used=json.loads((E/'ID-PREFLIGHT.json').read_text())['used'];assert n not in used;assert n not in [a['id'] for a in t['attempts']]
assert t['lean_charged']<100
assert t['lean_charged']<97 or 'Audit' in module
assert n not in [39897,39898,39899] or 'Audit' in module
t['next_env_j_id']=n+1;t['attempts'].append(dict(id=n,module=module));tp.write_text(json.dumps(t,indent=2)+'\n')
assert not json.loads((E/'H4-library-verification.json').read_text())['mismatches']
imports=re.findall(r'^import (\S+)',p.read_text(),re.M)
code='''from pathlib import Path
import json,hashlib
D=Path(DIR);B=D.parent
sent=B/'r1-privacy-build-integration-20261019/evidence/sent.txt'
if sent.exists():
 for line in sent.read_text().splitlines():
  cols=line.split()
  if len(cols)>2 and cols[2]==str(ATTEMPT):raise SystemExit('used env-J ID in shared sent.txt')
if (B/'aspis-fs-generic-20261006/evidence'/('out-'+str(ATTEMPT)+'.log')).exists():raise SystemExit('used env-J output ID')
for root in B.glob('codex-*'):
 for pat in ['*'+str(ATTEMPT)+'*.json','candidate/*'+str(ATTEMPT)+'*']:
  for q in root.glob(pat):raise SystemExit('existing private receipt for ID: '+str(q))
e=json.loads((B/'r1-privacy-build-integration-20261019/env/J.json').read_text());e['LEAN_PATH']=str(B/'aspis-joint-20261019/objects')+':'+e['LEAN_PATH'];(D/'env-J.json').write_text(json.dumps(e));r={}
for m in IMPORTS:
 for d in [str(D/'lean-objects')]+e['LEAN_PATH'].split(':'):
  p=Path(d)/(m.replace('.','/')+'.olean')
  if p.exists():r[m]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest());break
 else:raise SystemExit('missing object '+m)
# Lean resolves the first R1Z directory as a unit: populate only private object links.
for root in e['LEAN_PATH'].split(':'):
 for src in (Path(root)/'R1Z').rglob('*.olean'):
  dst=D/'lean-objects/R1Z'/src.relative_to(Path(root)/'R1Z');dst.parent.mkdir(parents=True,exist_ok=True)
  if src.exists() and not dst.exists() and not dst.is_symlink():dst.symlink_to(src)
# A private h5 build must never write through an inherited object symlink.
if H5MODULE:
 dst=D/'lean-objects'/(H5MODULE+'.olean')
 if dst.is_symlink():dst.unlink()
 elif dst.exists():raise SystemExit('h5 output already exists; inspect instead of overwriting')
(D/'lean-sources/R1Z').mkdir(parents=True,exist_ok=True);(D/'lean-objects/R1Z').mkdir(parents=True,exist_ok=True)
print(json.dumps(r,sort_keys=True))
'''.replace('DIR',repr(D)).replace('IMPORTS',repr(imports)).replace('ATTEMPT',str(n)).replace('H5MODULE',repr(module if h5 else None))
r=subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True)
if r.returncode:(E/f'{n}-preflight-error.txt').write_text(r.stderr+r.stdout);raise SystemExit(r.stderr+r.stdout)
deps=json.loads(r.stdout);fp=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest();meta=dict(attempt=n,module=module,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),worktree_source_dirty=bool(subprocess.check_output(['git','status','--porcelain','--',str(p)],text=True).strip()),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),deps_fingerprint=fp,dependency_objects=deps)
blob=subprocess.run(['git','rev-parse','HEAD:'+str(p.relative_to(R))],text=True,capture_output=True)
meta['source_git_blob_at_head']=blob.stdout.strip() if blob.returncode==0 else None
meta['source_worktree_git_blob']=subprocess.check_output(['git','hash-object',str(p)],text=True).strip()
if h5:meta['h5_source_pin']=h5
# Refuse every previously charged identical source/dependency pair, including failures.
charged_ids={a['id'] for a in t['attempts'] if a.get('charged')}
for prior in list(E.glob('*-submission.json'))+list((E.parent/'batch2b').glob('*-submission.json'))+list((E.parent/'batch2c').glob('*-submission.json')):
 q=json.loads(prior.read_text())
 if q.get('attempt') in charged_ids and q.get('source_sha256')==meta['source_sha256'] and q.get('deps_fingerprint')==fp:
  t['attempts'][-1]['uncharged_reason']='duplicate source/dependency refusal before compiler launch'
  tp.write_text(json.dumps(t,indent=2)+'\n')
  raise SystemExit('REFUSED unchanged charged source/dependency pair from '+str(q['attempt']))
(E/f'{n}-submission.json').write_text(json.dumps(meta,indent=2)+'\n');(E/f'{n}-source.lean.txt').write_bytes(p.read_bytes())
subprocess.run(['scp','-q',str(p),H+':'+D+'/lean-sources/'+module+'.lean'],check=True)
cmd=['timeout','900','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',D+'/env-J.json',D+'/lean-objects',D+'/lean-sources',D+'/lean-objects/'+module+'.olean',D+'/lean-sources/'+module+'.lean','7000']
label='batch2d-lean-'+str(n)
a=subprocess.run(['ssh',H,shlex.join(['python3',D+'/native.py','candidate',label,*cmd])],text=True,capture_output=True);(E/f'{n}-launcher.log').write_text(a.stdout+a.stderr);print(a.stdout+a.stderr)
res=subprocess.run(['ssh',H,'cat '+D+'/candidate/'+label+'/receipt/receipt.json'],text=True,capture_output=True)
if res.returncode:
 for name in ['admission-before.json','reservation.log','admission-barrier.json','output.log']:
  rr=subprocess.run(['ssh',H,'cat '+D+'/candidate/'+label+'/'+name],text=True,capture_output=True)
  if rr.returncode==0:(E/f'{n}-{name}').write_text(rr.stdout)
 bf=E/f'{n}-admission-barrier.json'
 if bf.exists() and json.loads(bf.read_text()).get('error'):
  br=json.loads(bf.read_text());(E/'HOST-BARRIER-STOP.json').write_text(json.dumps(dict(attempt=n,module=module,error=br['error'],compiler_launched=False,rule='local-lean.txt rule6'),indent=2)+'\n')
  raise SystemExit('STOP: infrastructure barrier failure: '+br['error'])
 print('UNCHARGED refusal; preserve cooldown');sys.exit(a.returncode or 1)
rec=json.loads(res.stdout);t=json.loads(tp.read_text());t['lean_charged']+=1;t['remaining_lean_budget']=100-t['lean_charged'];t['lean_attempts']=t['lean_charged'];t['used_ids']=[a['id'] for a in t['attempts']];t['next_id']=t['next_env_j_id'];t['attempts'][-1].update(charged=True,exit=rec['exit_status']);tp.write_text(json.dumps(t,indent=2)+'\n')
for name in ['stdout.log','stderr.log','time.log']:
 v=subprocess.check_output(['ssh',H,'cat '+D+'/candidate/'+label+'/receipt/'+name],text=True);(E/f'{n}-{name}').write_text(v)
 if name=='stdout.log':
  meta['axiom_output']=v
  if rec['exit_status']==0:print(module,n,'PASS; axiom output retained in receipt')
  else:print(v)
rec['print_axioms']=[line for line in meta.get('axiom_output','').splitlines() if 'axioms' in line] if rec['exit_status']==0 else 'compile failed; no accepted theorem from this attempt'
rec['native_wrapper_revision']=rec.pop('source_revision');meta.update(rec)
ax=[dict(declaration=m[1],axioms=[] if m[3] is None else [s.strip() for s in m[3].replace('\n',' ').split(',') if s.strip()]) for m in re.finditer(r"^'([^'\n]+)' (does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",meta.get('axiom_output',''),re.M)]
meta['parsed_axioms']=ax
meta['accepted_axioms']=all(set(q['axioms'])<={'propext','Classical.choice','Quot.sound'} for q in ax) and (rec['exit_status']!=0 or len(ax)==len(re.findall(r'^#print axioms ',p.read_text(),re.M)))
(E/f'{n}.json').write_text(json.dumps(meta,indent=2)+'\n');sys.exit(rec['exit_status'] if meta['accepted_axioms'] else 1)
