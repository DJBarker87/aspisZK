"""Local receipt aggregation; no compiler, native gate, or arithmetic release job."""
from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for p in sorted(E.glob('*-receipt.json')):
 x=json.loads(p.read_text());label=p.name.removesuffix('-receipt.json');tim=E/(label+'-time.log');out=E/(label+'-output.log');s=tim.read_text() if tim.exists() else ''
 get=lambda pattern:re.search(pattern,s)
 rss=get(r'Maximum resident set size \(kbytes\): (\d+)');swap=get(r'Swaps: (\d+)');elapsed=get(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([0-9:.]+)')
 wall=0
 if elapsed:
  for part in elapsed[1].split(':'):wall=60*wall+float(part)
 x.update(label=label,peak_rss_kib=int(rss[1]) if rss else None,swaps=int(swap[1]) if swap else None,gnu_wall_seconds=wall if elapsed else None,raw_receipt_sha256=sha(p),output_sha256=sha(out),time_sha256=sha(tim) if tim.exists() else None,resource_caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,Lean_M=7000 if label.startswith('lean') else None),source_revision_qualification='Raw source_revision is retained; deployed Rust inputs additionally bind to candidate-source-pins.json. Only final audited core receives independent formal credit; bridge compiles are provenance-gated.')
 if label.startswith('lean'):
  text=out.read_text();x['axioms']=re.findall(r"'[^\n]+' (?:depends on axioms:\s*\[[\s\S]*?\]|does not depend on any axioms)",text)
  x['formal_credit']='independent core audit' if label=='lean62797' else 'development only; failed, superseded, or provenance-gated'
  if label=='lean62797':assert x['exit']==0 and len(x['axioms'])==8 and 'sorryAx' not in str(x['axioms'])
 rows.append(x)
r=dict(native_scopes=sum(x['label'].startswith('native') for x in rows),lean_attempts=sum(x['label'].startswith('lean') for x in rows),kani=0,native_failures=[x['label'] for x in rows if x['label'].startswith('native') and x['exit']],lean_failures=[x['label'] for x in rows if x['label'].startswith('lean') and x['exit']],peak_rss_kib=max(x['peak_rss_kib'] or 0 for x in rows),total_gnu_wall_seconds=sum(x['gnu_wall_seconds'] or 0 for x in rows),all_swaps_zero=all(x['swaps']==0 for x in rows),admission_all_compliant=all(x['admission_exit']==0 and x['admission_allowed'] is True for x in rows),ids=[x.get('attempt',int(x['label'][4:])) for x in rows if x['label'].startswith('lean')],scopes=rows)
r['budgets'] = dict(prior_lean=sum(62700<=i<=62799 for i in r['ids']), resume_lean=sum(63000<=i<=63099 for i in r['ids']), prior_native=sum(x['label'].startswith('native') and not x['label'].startswith('nativeR') for x in rows), resume_native=sum(x['label'].startswith('nativeR') for x in rows), resume_lean_limit=85,resume_native_limit=22)
assert r['budgets']['resume_lean']==85 and r['budgets']['resume_native']<=22 and r['admission_all_compliant'] and all(62700<=i<=62799 or 63000<=i<=63099 for i in r['ids'])
accepted={x['attempt']:x['module'] for x in json.loads((E/'final-cohort-post.json').read_text())['modules']}
for x in rows:
 if x['label'].startswith('lean630'):
  n=int(x['label'][4:]);x['formal_credit']='final accepted source/model cohort' if n in accepted else 'historical failed or superseded attempt; no independent final credit'
  x['source_revision_qualification']='Raw revision plus per-attempt source snapshot/hash and dependency_objects pins; final-cohort-post.json validates the accepted closure. Source model credit does not discharge open native leaf or compiler obligations.'

(E/'attempts.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:v for k,v in r.items() if k!='scopes'},indent=2))
# Current final-source pins; these do not invent source snapshots for failed iterations.
pins=[]
for p in sorted(E.glob('PV_DIAG2_*.lean')):
 pins.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size,git_blob=subprocess.check_output(['git','hash-object',str(p)],text=True).strip(),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()))
(E/'final-source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
