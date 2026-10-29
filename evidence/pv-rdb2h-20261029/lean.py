"""One unchanged pinned module per admitted capped replay attempt; no source writes."""
from pathlib import Path
import sys,subprocess,json,hashlib,re,shlex
from cooldown import check_ready
check_ready()
E=Path(__file__).resolve().parent;R=E.parents[1];D='/home/dombarker/project-offloads/codex-pv-rdb2h-20261029';F='/home/dombarker/project-offloads/codex-pv-rdb2f-20261029';O='/home/dombarker/project-offloads/codex-pv-rdb2e-20261029/lean-objects';H='dombarker@100.108.41.90'
n=int(sys.argv[1]);m=sys.argv[2];assert 64300<=n<=64399;assert n<64397 or any(t in m for t in ['Audit','Replay'])
p=json.loads((E/'plan.json').read_text());r=next(x for x in p['objects'] if x['module']==m);rel=m.replace('.','/');src=F+'/lean-sources/'+rel+'.lean';out=O+'/'+rel+'.olean';assert not(E/f'lean-{n}/receipt.json').exists()
meta=dict(attempt=n,module=m,source_path=r['source']['path'],source_blob=r['source']['blob'],source_sha256=r['source']['sha256'],source_revision=p['revision'],previous_object_sha256=r['object_sha256'],environment='exact preflight.prior_environment; original leading prefix',imports=r['imports'])
(E/f'{n}-submission.json').write_text(json.dumps(meta,indent=2)+'\n')
code='from pathlib import Path; import hashlib; s=Path('+repr(src)+'); assert hashlib.sha256(s.read_bytes()).hexdigest()=='+repr(meta['source_sha256'])+'; o=Path('+repr(out)+'); assert not o.exists(); o.parent.mkdir(parents=True,exist_ok=True)'
subprocess.run(['ssh',H,'python3 -c '+shlex.quote(code)],check=True)
cmd=['timeout','900','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',D+'/env-J.json',O,F+'/lean-sources',out,src,'7000']
run=subprocess.run([sys.executable,str(E/'scope.py'),f'lean-{n}','unchanged exact-environment focused Lean replay',*cmd],capture_output=True,text=True)
(E/f'{n}-driver.log').write_text(run.stdout+run.stderr)
q=E/f'lean-{n}/receipt.json'
if q.exists():
 j=json.loads(q.read_text());j['execution_revision']=j['source_revision'];j.update(meta);s=(q.parent/'output.log').read_text();j['print_axioms']=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",s,re.S)
 if run.returncode==0:
  code='from pathlib import Path; import hashlib,json; p=Path('+repr(out)+'); print(json.dumps(dict(object_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size,companions=[dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size) for q in [p.with_suffix(".ir"),Path(str(p)+".server"),Path(str(p)+".private")] if q.exists()])))'
  data=json.loads(subprocess.check_output(['ssh',H,'python3 -c '+shlex.quote(code)],text=True));j.update(data);j['matches_rdb2f']=data['object_sha256']==r['object_sha256']
 q.write_text(json.dumps(j,indent=2)+'\n');print(n,m,'exit',run.returncode,'wall',j['wall'],'hash_matches',j.get('matches_rdb2f'),flush=True)
else:print(run.stdout[-2000:]+run.stderr[-2000:],flush=True)
sys.exit(run.returncode)
