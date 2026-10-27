"""One private-source Env-J proof attempt, using the standing runner and barrier."""
from pathlib import Path
import hashlib,json,re,shlex,subprocess,sys
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-alib-20261027'
D='/home/dombarker/project-offloads/codex-pv-alib-20261027'
H='dombarker@100.108.41.90'; B='/home/dombarker/project-offloads'
G=B+'/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
n=int(sys.argv[1]); m=sys.argv[2]; assert 37600<=n<=37699
assert m.startswith('R1Z/PV_AL_')
p=R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean'); assert p.exists()
tp=E/'TALLY.json'; t=json.loads(tp.read_text())
assert n not in t['used_ids']+t['excluded_prior_ids'] and t['lean_charged']<100
assert n<37697 or 'Audit' in m
assert json.loads((E/'resume3-external-verification.json').read_text())['ok']
assert json.loads((E/'resume3-project-preflight.json').read_text())['ok']
sha=hashlib.sha256(p.read_bytes()).hexdigest()
def ssh(c):return subprocess.run(['ssh',H,c],text=True,capture_output=True)
imports=re.findall(r'^import (\S+)',p.read_text(),re.M)
code='''from pathlib import Path
import json,hashlib
d=Path(DIR); b=d.parent
e=json.loads((b/'r1-privacy-build-integration-20261019/env/J.json').read_text())
roots=[b/'aspis-joint-20261019/objects',b/'codex-pv-cblib-20261027/lean-objects']+[Path(x) for x in e['LEAN_PATH'].split(':')]
e['LEAN_PATH']=':'.join(map(str,roots));(d/'env-J.json').write_text(json.dumps(e))
o=d/'lean-objects';o.mkdir(exist_ok=True)
for root in roots:
 for src in (root/'R1Z').glob('*.olean'):
  dst=o/'R1Z'/src.name;dst.parent.mkdir(exist_ok=True)
  if src.exists() and not dst.exists() and not dst.is_symlink():dst.symlink_to(src)
r={}
for m in IMPORTS:
 for root in [o]+roots:
  q=root/(m.replace('.','/')+'.olean')
  if q.exists():r[m]={'path':str(q),'sha256':hashlib.sha256(q.read_bytes()).hexdigest()};break
 else:raise SystemExit('missing object '+m)
(d/'lean-sources/R1Z').mkdir(parents=True,exist_ok=True)
print(json.dumps(r,sort_keys=True))
'''.replace('DIR',repr(D)).replace('IMPORTS',repr(imports))
r=subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stdout+r.stderr
deps=json.loads(r.stdout);fp=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest()
assert not any(x.get('charged') and x.get('sha256')==sha and x.get('deps_fingerprint')==fp for x in t['attempts'])
meta=dict(id=n,module=m,sha256=sha,deps_fingerprint=fp,dependency_objects=deps,
 source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
t['used_ids'].append(n);t['attempts'].append(meta);tp.write_text(json.dumps(t,indent=2)+'\n')
(E/f'{n}-source.lean.txt').write_bytes(p.read_bytes())
r=ssh(f'mkdir -p {D}/runs/{n}; python3 {G}/reservation.py {D}/runs/{n}/admission-before.json > {D}/runs/{n}/reservation.log 2>&1')
ad=ssh(f'cat {D}/runs/{n}/admission-before.json')
(E/f'{n}-admission.json').write_text(ad.stdout)
if r.returncode!=0 or not json.loads(ad.stdout).get('allowed'):
 print('UNCHARGED admission refusal',r.returncode,{k:json.loads(ad.stdout).get(k) for k in ['utc','allowed','error','bounded_reserved_bytes','safe_limit_bytes']});sys.exit(78)
subprocess.run(['scp','-q',str(p),H+':'+D+'/lean-sources/'+m+'.lean'],check=True)
cmd=['timeout','900','python3',B+'/aspis-fs-generic-20261006/evidence/run2.py',D+'/env-J.json',D+'/lean-objects',D+'/lean-sources',D+'/lean-objects/'+m+'.olean',D+'/lean-sources/'+m+'.lean','7000']
run=['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',G+'/barrier.py',D+f'/runs/{n}/admission-barrier.json','/usr/bin/time','-v','-o',D+f'/runs/{n}/time.log',*cmd]
r=ssh(shlex.join(run)+f' > {D}/runs/{n}/output.log 2>&1');status=r.returncode
for name in ['output.log','time.log','admission-barrier.json']:
 v=ssh(f'cat {D}/runs/{n}/{name}')
 if v.returncode==0:(E/f'{n}-{name}').write_text(v.stdout)
bar=json.loads((E/f'{n}-admission-barrier.json').read_text())
if not bar.get('allowed'):print('UNCHARGED barrier refusal');sys.exit(78)
t=json.loads(tp.read_text());t['lean_charged']+=1;t['attempts'][-1]['charged']=True
tp.write_text(json.dumps(t,indent=2)+'\n')
log=(E/f'{n}-output.log').read_text();tim=(E/f'{n}-time.log').read_text()
def field(s):
 x=re.search(s+':\\s*(.+)',tim);return x[1] if x else None
meta.update(target=cmd,exit=status,wall=field(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\)'),peak_rss_kib=field(r'Maximum resident set size \(kbytes\)'),swap=field('Swaps'),axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log,re.S),limits=dict(Lean_M=7000,MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64))
(E/f'{n}.json').write_text(json.dumps(meta,indent=2)+'\n')
print(log);print(json.dumps({k:meta[k] for k in ['id','exit','wall','peak_rss_kib','swap']}))
sys.exit(status)
