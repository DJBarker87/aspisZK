from pathlib import Path
import hashlib,json,re,shlex,subprocess,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-batch2-20261027/batch2b';D='/home/dombarker/project-offloads/codex-pv-batch2-20261027';H='dombarker@100.108.41.90'
n=int(sys.argv[1]);module=sys.argv[2];assert 52000<=n<=52499
p=R/'docs/research/v8-r0-zk-20261009/lean'/(module+'.lean');assert p.name.startswith('PV_B2_')
tp=E/'TALLY.json';t=json.loads(tp.read_text());used=json.loads((E/'ID-PREFLIGHT.json').read_text())['used'];assert n not in used;assert n not in [a['id'] for a in t['attempts']]
assert t['lean_charged']<100
assert t['lean_charged']<97 or 'Audit' in module
assert n not in [52497,52498,52499] or 'Audit' in module
t['next_env_j_id']=n+1;t['attempts'].append(dict(id=n,module=module));tp.write_text(json.dumps(t,indent=2)+'\n')
imports=re.findall(r'^import (\S+)',p.read_text(),re.M)
code='''from pathlib import Path
import json,hashlib
D=Path(DIR);B=D.parent;e=json.loads((B/'r1-privacy-build-integration-20261019/env/J.json').read_text());e['LEAN_PATH']=str(B/'aspis-joint-20261019/objects')+':'+e['LEAN_PATH'];(D/'env-J.json').write_text(json.dumps(e));r={}
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
(D/'lean-sources/R1Z').mkdir(parents=True,exist_ok=True);(D/'lean-objects/R1Z').mkdir(parents=True,exist_ok=True)
print(json.dumps(r,sort_keys=True))
'''.replace('DIR',repr(D)).replace('IMPORTS',repr(imports))
r=subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True)
if r.returncode:(E/f'{n}-preflight-error.txt').write_text(r.stderr+r.stdout);raise SystemExit(r.stderr+r.stdout)
deps=json.loads(r.stdout);fp=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest();meta=dict(attempt=n,module=module,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),worktree_source_dirty=bool(subprocess.check_output(['git','status','--porcelain','--',str(p)],text=True).strip()),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),deps_fingerprint=fp,dependency_objects=deps)
(E/f'{n}-submission.json').write_text(json.dumps(meta,indent=2)+'\n');(E/f'{n}-source.lean.txt').write_bytes(p.read_bytes())
subprocess.run(['scp','-q',str(p),H+':'+D+'/lean-sources/'+module+'.lean'],check=True)
cmd=['timeout','900','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',D+'/env-J.json',D+'/lean-objects',D+'/lean-sources',D+'/lean-objects/'+module+'.olean',D+'/lean-sources/'+module+'.lean','7000']
label='batch2b-lean-'+str(n)
a=subprocess.run(['ssh',H,shlex.join(['python3',D+'/native.py','candidate',label,*cmd])],text=True,capture_output=True);(E/f'{n}-launcher.log').write_text(a.stdout+a.stderr);print(a.stdout+a.stderr)
res=subprocess.run(['ssh',H,'cat '+D+'/candidate/'+label+'/receipt/receipt.json'],text=True,capture_output=True)
if res.returncode:
 for name in ['admission-before.json','reservation.log','admission-barrier.json','output.log']:
  rr=subprocess.run(['ssh',H,'cat '+D+'/candidate/'+label+'/'+name],text=True,capture_output=True)
  if rr.returncode==0:(E/f'{n}-{name}').write_text(rr.stdout)
 print('UNCHARGED refusal; preserve cooldown');sys.exit(a.returncode or 1)
rec=json.loads(res.stdout);t=json.loads(tp.read_text());t['lean_charged']+=1;t['lean_attempts']=t['lean_charged'];t['used_ids']=[a['id'] for a in t['attempts']];t['next_id']=t['next_env_j_id'];t['attempts'][-1].update(charged=True,exit=rec['exit_status']);tp.write_text(json.dumps(t,indent=2)+'\n')
for name in ['stdout.log','stderr.log','time.log']:
 v=subprocess.check_output(['ssh',H,'cat '+D+'/candidate/'+label+'/receipt/'+name],text=True);(E/f'{n}-{name}').write_text(v)
 if name=='stdout.log':
  meta['axiom_output']=v
  if rec['exit_status']==0:print('\n'.join(line for line in v.splitlines() if 'axioms' in line))
  else:print(v)
rec['print_axioms']=[line for line in meta.get('axiom_output','').splitlines() if 'axioms' in line] if rec['exit_status']==0 else 'compile failed; no accepted theorem from this attempt'
rec['native_wrapper_revision']=rec.pop('source_revision');meta.update(rec);meta['accepted_axioms']=not any(x in meta.get('axiom_output','') for x in ['sorryAx','_native.','axiom ']);(E/f'{n}.json').write_text(json.dumps(meta,indent=2)+'\n');sys.exit(rec['exit_status'] if meta['accepted_axioms'] else 1)
