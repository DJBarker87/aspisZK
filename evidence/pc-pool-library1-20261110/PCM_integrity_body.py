"""Serial final retention checks, no proof replay or shared mutation."""
from pathlib import Path
import json,hashlib,lzma,sys,time,os
B=Path.cwd();mode=sys.argv[1];assert mode in ['retention','final']
E=B/'PCM_audit'/mode;E.mkdir(parents=True,exist_ok=True);data=json.loads((B/'PCM_INTEGRITY_INPUTS.json').read_text());start=time.monotonic()
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  while block:=f.read(1024*1024):h.update(block)
 return h.hexdigest()
result=dict(mode=mode,supporting_only=True,required_gate_pass=False)
if mode=='retention':
 manifest=json.loads((B/'PCM_EXTRACT_SOURCE_MANIFEST.json').read_text())
 for n,r in manifest.items():assert sha(B/'PCM_frozen_src'/n)==r['sha256'],n
 pool=[n for n in manifest if n.startswith('programs/aspis-pool/')];assert len(pool)==20
 for r in data['freeze']['sources']:
  n=Path(r['path']).name;assert sha(B/'PCM_sources'/n)==r['sha256'],n
 p=B/'PCM_CONTEXT_IMPORTS.json.xz';assert sha(p)==data['context_sha256']
 rows=json.loads(lzma.decompress(p.read_bytes()))+data['other_imports'];seen={};total=0
 for r in rows:
  dst=Path(r['destination']);assert str(dst).startswith(str(B)+'/'),str(dst)
  assert 'codex-cx-tx2-entry5-20261110' not in r['source'],r['source']
  if str(dst)in seen:assert seen[str(dst)]==r['sha256'];continue
  seen[str(dst)]=r['sha256'];assert sha(dst)==r['sha256'],str(dst)
  src=Path(r['source'])
  if src.exists():assert (src.stat().st_dev,src.stat().st_ino)!=(dst.stat().st_dev,dst.stat().st_ino),str(dst)
  total+=dst.stat().st_size
 result.update(frozen_source_files=len(manifest),pool_files=len(pool),frozen_spec_files=len(data['freeze']['sources']),imported_files=len(seen),imported_bytes=total,context_sha256=data['context_sha256'])
else:
 receipts=[]
 for p in sorted(B.glob('PCM_L[0-9][0-9][0-9]/receipt.json')):
  r=json.loads(p.read_text());receipts.append(r);limits=r['limits']
  assert limits['memory.high']=='6442450944'and limits['memory.max']=='8589934592'and limits['memory.swap.max']=='0'and limits['pids.max']=='64',r['attempt']
  assert r['swaps']=='0',r['attempt']
 assert len(receipts)==199,len(receipts)
 roots=json.loads((B/'PCM_AUDIT_ROOTS.json').read_text());walked=[]
 for i,g in enumerate(roots['groups']):
  a=json.loads((B/'PCM_audit'/('proof'+str(i))/'validation.json').read_text());assert a['validated']is True
  assert sorted(z['root']for z in a['results'])==sorted(g)
  for z in a['results']:assert set(z['walked_axioms'])<={'Classical.choice','Quot.sound','propext'}and z['equal']is True
  walked+=a['results']
 assert sorted(x['root']for x in walked)==sorted(roots['roots'])
 fixture=json.loads((B/'PCM_audit/fixtures/validation.json').read_text());assert fixture['validated']and fixture['results']==data['fixtures']and len(fixture['results'])==8
 scan=json.loads((B/'PCM_audit/scan/validation.json').read_text());assert scan['validated']is True
 full=json.loads((B/'PCM_audit/fullimport/validation.json').read_text());assert full['validated']is False and full['exit_status']!=0
 result.update(prior_scopes=len(receipts),new_roots=len(walked),fixtures=8,raw_standard_only=True,supporting_scan_pass=True,full_gate='FAILED_MISSING_PROHIBITED_OR_UNEXPORTED_CONTEXT',peak_rss_kib=max(int(r['peak_rss_kib'])for r in receipts),total_prior_wall_seconds=sum(r['wall_seconds']for r in receipts),swaps=0)
result.update(validated=True,wall_seconds=time.monotonic()-start)
(E/'validation.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps(result))
