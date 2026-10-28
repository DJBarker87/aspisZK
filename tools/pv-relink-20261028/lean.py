from pathlib import Path
import hashlib,json,subprocess,sys,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-relink-20261028';D='/home/dombarker/project-offloads/codex-pv-relink-20261028';H='dombarker@100.108.41.90'
n=int(sys.argv[1]);m=sys.argv[2].replace('/','.');assert 43700<=n<=43799
assert n<43797 or any(x in m for x in ['Audit','Replay'])
pre=json.loads((E/'preflight.json').read_text());assert all(x['ok'] for x in pre['external'])
res=json.loads((E/'source-resolution.json').read_text())['modules']
if m in res:
 x=res[m];p=R/x['path'];b=subprocess.check_output(['git','cat-file','blob',x['blob']]) if 'blob' in x else p.read_bytes()
else:
 assert m.startswith('R1Z.PV_RL_');p=R/'docs/research/v8-r0-zk-20261009/lean'/(m.replace('.','/')+'.lean');b=p.read_bytes();assert subprocess.check_output(['git','show','HEAD:'+str(p.relative_to(R))])==b
assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b',b.decode())
ledger=E/'attempts.json';t=json.loads(ledger.read_text()) if ledger.exists() else []
prior=[x for x in t if x['id']==n]
retry=bool(prior)
if retry:
 assert len(prior)==1 and not prior[0].get('charged') and prior[0]['sha256']==hashlib.sha256(b).hexdigest()
 a=json.loads((E/f'{n}-upload-admission.json').read_text());assert 'FileNotFoundError' in (a.get('error') or '') or 'ENODEV' in (a.get('error') or '')
 (E/f'{n}-transient-upload-refusal.json').write_text(json.dumps(a,indent=2)+'\n')
assert len([x for x in t if x.get('charged')])<100
x=dict(id=n,module=m,sha256=hashlib.sha256(b).hexdigest(),revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),imports=re.findall(r'^import (\S+)',b.decode(),re.M));
if retry:t[-1]=x
else:t.append(x)
ledger.write_text(json.dumps(t,indent=2)+'\n')
(E/f'{n}-source.lean.txt').write_bytes(b)
p_remote=D+'/lean-sources/'+m.replace('.','/')+'.lean'
gate='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
ad=subprocess.run(['ssh',H,f'mkdir -p {D}/{n}; python3 {gate}/reservation.py {D}/{n}/upload-admission.json > {D}/{n}/upload-admission.log 2>&1'],text=True,capture_output=True)
q=subprocess.run(['ssh',H,f'cat {D}/{n}/upload-admission.json'],text=True,capture_output=True)
(E/f'{n}-upload-admission.json').write_text(q.stdout)
if ad.returncode!=0 or json.loads(q.stdout).get('allowed') is not True:
 print('UNCHARGED upload admission refusal',ad.returncode,{k:json.loads(q.stdout).get(k) for k in ['utc','allowed','error','bounded_reserved_bytes']});sys.exit(78)
subprocess.run(['scp','-q',str(E/f'{n}-source.lean.txt'),H+':'+p_remote],check=True)
cmd=['timeout','900','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',D+'/env-J.json',D+'/lean-objects',D+'/lean-sources',D+'/lean-objects/'+m.replace('.','/')+'.olean',p_remote,'7000']
r=subprocess.run([sys.executable,str(R/'tools/pv-relink-20261028/scope.py'),str(n),'Lean',*cmd])
p=E/str(n)/'receipt.json';t=json.loads(ledger.read_text());t[-1]['charged']=p.exists();t[-1]['exit']=r.returncode
if p.exists():
 j=json.loads(p.read_text());j.update(x);j['dependency_source_resolution']='../source-resolution.json';j['preflight']='../preflight.json';p.write_text(json.dumps(j,indent=2)+'\n')
ledger.write_text(json.dumps(t,indent=2)+'\n');sys.exit(r.returncode)
