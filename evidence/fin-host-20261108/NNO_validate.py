"""Receipt/archive/source hygiene; no prover replay."""
from pathlib import Path
import json,lzma,hashlib,re,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=[json.loads(p.read_text())for p in sorted(E.glob('NNO_L*/receipt.json'))];assert len(r)==24
standard={'propext','Classical.choice','Quot.sound'};missing=[]
for x in r:
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert x['swaps']=='0'
 ad=json.loads((E/(x['attempt']+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed']is True
 disk=json.loads((E/(x['attempt']+'-disk-0.json')).read_text());assert disk['free']>=40_000_000_000
 for f,h in x['source_hashes'].items():assert sha(E/x['attempt']/'sources'/f)==h
 if isinstance(x['print_axioms'],list):
  for l in x['print_axioms']:
   axioms=set(re.search(r'\[([^]]*)\]',l)[1].split(', '))if '['in l else set();assert axioms<=standard,(x['attempt'],l)
cols=['attempt','target','exit','wall_s','peak_rss_kib','swap','source_revision','source_sha256','olean_sha256','printed_axioms','receipt']
out=['\t'.join(cols)]
for x in r:
 p=E/(x['attempt']+'-object.json');o=json.loads(p.read_text())if p.exists()else{}
 vals=[x['attempt'],x['module'],x['exit_status'],x['wall_seconds'],x['peak_rss_kib'],x['swaps'],x['source_revision'],json.dumps(x['source_hashes'],separators=(',',':')),o.get('sha256','-'),json.dumps(x['print_axioms'],separators=(',',':')),x['attempt']+'/receipt.json'];out.append('\t'.join(map(str,vals)))
(E/'NNO_COMPILE.tsv').write_text('\n'.join(out)+'\n')
archives=[]
for p in E.rglob('*.xz'):
 h=p.with_suffix('.sha256');assert h.exists(),p
 data=lzma.open(p).read();assert hashlib.sha256(data).hexdigest()==h.read_text().strip();archives.append(dict(path=str(p.relative_to(E)),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)))
# Draft sources are untouched; source snapshots consumed by compilation are byte-identical.
for folder,glob in [('nvr-20261108','NVR_*.lean'),('fin-20261108','FIN_*.lean')]:
 for p in (R/'evidence'/folder).glob(glob):
  original=subprocess.check_output(['git','show','953e3af13bb:'+str(p.relative_to(R))],cwd=R);assert hashlib.sha256(original).hexdigest()==sha(p)
for p in (R/'evidence/rowspec-lead-20261107').glob('*.lean'):
 original=subprocess.check_output(['git','show','953e3af13bb:'+str(p.relative_to(R))],cwd=R);assert hashlib.sha256(original).hexdigest()==sha(p)
assert subprocess.run(['git','diff','--quiet','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','HEAD','--','crates','programs/r1-cost-probe','Cargo.lock'],cwd=R).returncode==0
large=[str(p)for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000];assert not large
proof=json.loads((E/'NNO_audit/final/proof0.json').read_text());assert proof['exit_status']==0 and len(proof['results'])==5
for z in proof['results']:assert z['equal']and set(z['walked_axioms'])<=standard
resources=dict(scopes=24,budget=24,wall_seconds=sum(x['wall_seconds']for x in r),peak_rss_kib=max(int(x['peak_rss_kib'])for x in r),swaps=0,kani=0,extraction=0,scope_exits={x['attempt']:x['exit_status']for x in r},limits=r[0]['limits'])
(E/'NNO_RESOURCES.json').write_text(json.dumps(resources,indent=1)+'\n')
validation=dict(status='INCOMPLETE_COMBINED_NFX',receipt_hygiene='PASS',frozen_source='PASS',draft_source_identity='PASS',RSL_unchanged='PASS',archives=archives,standard_axioms='PASS',raw_FIN='5/5 PASS',fixtures='8/8 PASS',scan='not executed: own driver elaboration error; corrected source untested',no_large_file=True,resource_review='retrospective FIN RSS review; no live stop receipt',row_credit=0)
(E/'NNO_VALIDATION.json').write_text(json.dumps(validation,indent=1)+'\n');print(json.dumps(dict(status=validation['status'],receipts=len(r),archives=len(archives),wall_seconds=resources['wall_seconds'],peak_rss_kib=resources['peak_rss_kib'])))
