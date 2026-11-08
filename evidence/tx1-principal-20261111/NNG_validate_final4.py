"""Validate final new-root audit and exact archived scope accounting."""
from pathlib import Path
import json,lzma,hashlib,re,subprocess
E=Path(__file__).resolve().parent;prefix='NNG_R4Final_'
def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
manifest=load(E/(prefix+'AUDIT_ROOTS.json'));roots=manifest['roots'];groups=manifest['groups']
assert len(roots)==len(set(roots));assert [r for g in groups for r in g]==roots
accepted={'propext','Classical.choice','Quot.sound'};allresults=[];audit_receipts=[]
for i,g in enumerate(groups):
 d=E/(prefix+'audit')/f'proof{i}';r=load(d/f'proof{i}.json');assert r['exit_status']==0,r
 assert r['swaps']=='0';results=r['results'];assert {a['root']for a in results}==set(g)
 for a in results:
  assert a['equal'] and set(a['collect_axioms'])==set(a['walked_axioms']) and set(a['walked_axioms'])<=accepted,a
 for p in d.glob('*.xz'):
  raw=lzma.decompress(p.read_bytes());assert sha(raw)==Path(str(p)[:-3]+'.sha256').read_text().strip(),p
 allresults+=results;audit_receipts.append(f'NNG_L{978+i}/receipt.json')
assert {a['root']for a in allresults}==set(roots)
for m,receipt in manifest['selected_receipts'].items():
 p=E/receipt;r=load(p);assert r['exit_status']==0
 src=E/(m+'.lean');gen=E/'NNG_generated'/(m+'.lean');snap=p.parent/'sources'/'NNG_generated'/(m+'.lean')
 assert src.read_bytes()==gen.read_bytes()==snap.read_bytes(),m
 log=(p.parent/'stdout.log').read_text();assert 'sorryAx'not in log,m
 print_roots=re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",log)
 assert all(r in roots or r in manifest['prior_roots_excluded'] for r in print_roots),m
candidate=next(a for a in allresults if a['root']=='AspisR1.NNG_Candidate328.candidate')
for a in ['NNG_L975','NNG_L976','NNG_L977']:
 r=load(E/a/'receipt.json');assert r['exit_status']==0,a
completed=set();archives=[]
for p in sorted(E.glob('NNG_ATTEMPTS*.jsonl'))+sorted(E.glob('NNG_ATTEMPTS*.jsonl.xz')):
 raw=lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes()
 if p.suffix=='.xz':assert sha(raw)==Path(str(p)[:-3]+'.sha256').read_text().strip();archives.append(dict(path=p.name,raw_sha256=sha(raw)))
 for line in raw.splitlines():
  r=json.loads(line)
  if r.get('kind')!='wait':completed.add(r['attempt'])
submitted={r['attempt']for l in (E/'NNG_TRANSPORT.jsonl').read_text().splitlines()if (r:=json.loads(l)).get('submitted')}
assert not submitted-completed,submitted-completed
used={'lean_link_audit':set(),'kani':set(),'extract':set()}
for a in completed|submitted:
 r=load(E/(a+'.json'));k=r['kind'];g='lean_link_audit'if k in ['lean','link','audit']else k
 if g in used:used[g].add(a)
counts={g:len(s)for g,s in used.items()};assert counts['lean_link_audit']<=830 and counts['extract']<=2 and counts['kani']<=10
oversized=[str(p.relative_to(E))for p in E.rglob('*')if p.is_file()and p.stat().st_size>20*1024*1024];assert not oversized,oversized
result=dict(complete=True,root_count=len(roots),groups=len(groups),candidate328=candidate,raw_equals_collector=True,accepted_axioms=sorted(accepted),combined='NNG_L975/receipt.json',driver='NNG_L976/receipt.json',optimized_link='NNG_L977/receipt.json',audits=audit_receipts,used=counts,scope_limits=dict(lean_link_audit=830,kani=10,extract=2),unresolved_submissions=[],attempt_archives=archives,candidate345=False,remaining='NNG_345_STAGE.md',credit_requested=0)
(E/(prefix+'VALIDATION.json')).write_text(json.dumps(result,indent=1)+'\n')
print(json.dumps(dict(roots=len(roots),groups=len(groups),used=counts,candidate328=True,candidate345=False)))
