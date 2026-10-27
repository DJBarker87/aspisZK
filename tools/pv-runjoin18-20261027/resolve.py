"""Resolve the producer closure exclusively through the two authorized records."""
import pathlib,json,subprocess,re,hashlib
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin18-20261027'
def git(s):return subprocess.check_output(['git','show',s],cwd=R)
rev=subprocess.check_output(['git','rev-parse','research'],cwd=R,text=True).strip()
ip='evidence/envj-rebuild-20261026/EJR_final-inventory.json'
fp='docs/research/100bit-spend-path-20261013/evidence/prover-commit47-20261022/final-source-freeze.json'
ib=git(rev+':'+ip);fb=(R/fp).read_bytes();inv=json.loads(ib);freeze=json.loads(fb)
selected={r['module'].replace('/','.'):r for r in inv['selected'] if r.get('resolution')}
frozen={r['module']:r for r in freeze['sources']};done={};missing=set()
def visit(m):
 if m in done or m in missing:return
 if m in selected:
  x=selected[m];r=x['resolution'];b=git(r['blob']);a=ip
  assert hashlib.sha256(b).hexdigest()==x['sha256']
 elif m in frozen:
  r=frozen[m];b=git(freeze['revision']+':'+r['path']);a=fp
  assert hashlib.sha256(b).hexdigest()==r['sha256']
 else:missing.add(m);return
 imports=re.findall(r'^import\s+(\S+)',b.decode(),re.M)
 done[m]=dict(authority=a,path=r['path'],sha256=hashlib.sha256(b).hexdigest(),imports=imports)
 for dep in imports:visit(dep)
visit('AspisR1ProducerRelease47.Funs')
out=dict(research_revision=rev,inventory_sha256=hashlib.sha256(ib).hexdigest(),freeze_sha256=hashlib.sha256(fb).hexdigest(),resolved=done,unpinned=sorted(missing),status='STOP STEP 1: closure module pinned by neither authorized record' if missing else 'resolved',endpoint_audit_rerun=False,endpoint_premises_removed=0)
(E/'endpoint-resolution.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
