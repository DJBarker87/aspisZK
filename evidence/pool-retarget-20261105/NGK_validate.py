"""Additive NGK gates; historical NFV checks remain unchanged."""
from pathlib import Path
import json,hashlib,re,subprocess,copy
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();J=lambda p:json.loads(p.read_text())
x=J(E/'NGK_PROVENANCE.json');g=J(E/'NGK_SOURCE_GRAPH.json');rename=x['namespace_map'];pat=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(map(re.escape,sorted(rename,key=len,reverse=True)))+r')(?![A-Za-z0-9_])')
def check_record(r):
 src=g[r['source_module']]['source'];assert H(src.encode())==r['source_sha256']
 body='\n'.join(l for l in src.splitlines() if not l.startswith('import '))+'\n';assert body==r['before_body']
 after=pat.sub(lambda m:rename[m.group()],body)
 if any('fully qualify' in c for c in r['changes']):after=re.sub(r'(?<![A-Za-z0-9_.])core.result.Result.map_err','AspisR1TerminalDecoder.core.result.Result.map_err',after)
 assert after==r['after_body'];assert H(after.encode())==r['transformed_body_sha256']
 p=E/(r['target_module']+'.lean');text=p.read_text();assert text.split('\n\n',1)[1].startswith(after)
 assert re.findall(r'^import ([\w.]+)',text,re.M)==r['imports_after']
 assert r['target_module']=='NGK_'+r['source_module']
for r in x['files']:check_record(r)
# Every final copied module must match a successful source snapshot; exclude
# the two retained failed elaborations rather than trusting their axiom output.
for record in x['files']:
 found=False
 for p in E.glob('NGK_L*/receipt.json'):
  rc=J(p)
  if rc['exit_status']!=0 or rc['module']!=record['target_module']:continue
  snapshot=p.parent/'sources'/'NGK_generated'/(record['target_module']+'.lean')
  if snapshot.is_file():found = snapshot.read_bytes()==(E/(record['target_module']+'.lean')).read_bytes()
  else:
   ref=J(Path(str(snapshot)+'.REFERENCE.json'));found=ref['sha256']==H((E/(record['target_module']+'.lean')).read_bytes())
  if found:break
 assert found,record['target_module']
assert len(x['files'])==48
mutations=[]
for label,key in [('body','after_body'),('before','before_body'),('source','source_sha256'),('owner','target_module'),('hash','transformed_body_sha256')]:
 r=copy.deepcopy(x['files'][0]);r[key]+='corrupt'
 try:check_record(r)
 except (AssertionError,FileNotFoundError):mutations.append(dict(name=label,rejected=True))
 else:raise AssertionError(label)
rows=[json.loads(l) for l in (E/'NGK_ATTEMPTS.jsonl').read_text().splitlines()]
assert len(rows)<=110 and len({r['attempt'] for r in rows})==len(rows)
for r in rows:
 rc=J(E/r['attempt']/'receipt.json');adm=J(E/(r['attempt']+'-admission.json'))
 assert adm['exit']==0 and adm['reservation']['allowed'] is True
 assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(rc['swaps'])=='0'
 assert all(k in rc for k in ['source_revision','source_hashes','deps_fingerprint','command','peak_rss_kib','wall_seconds','exit_status','print_axioms'])
assert subprocess.run(['git','diff','--quiet','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','--','crates','programs']).returncode==0
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<20*1024**2,p
for n in ['NFV','NFV_review_request','NFV_review_accounts','NFV_review_helper','NFV_review_C','NFV_prefix_check','NFV_error_coverage']:
 assert J(E/('NGK_REPLAY_'+n+'.json'))['exit_status']==0,n
(E/'NGK_VALIDATION.json').write_text(json.dumps(dict(provenance_records=48,only_imports_and_qualified_names=True,mutation_controls=mutations,attempts=len(rows),max_attempts=110,all_admission_caps_receipt_fields=True,unchanged_validators=7,shipped_files_byte_identical=True),indent=1)+'\n')
print('PASS',len(rows),'attempt receipts, 48 exact retarget records, 7 historical validators')
