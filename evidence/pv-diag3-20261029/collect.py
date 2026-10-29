"""Local evidence-only aggregation; no native gate or compiler."""
from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
scopes=[]
for p in sorted(E.glob('*-receipt.json')):
 r=json.loads(p.read_text());label=p.name.removesuffix('-receipt.json');out=E/(label+'-output.log');tim=E/(label+'-time.log');text=tim.read_text();val=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([0-9:.]+)',text);wall=None
 if val:
  wall=0
  for part in val[1].split(':'):wall=wall*60+float(part)
 axioms=re.findall(r"'[^\n]+' (?:depends on axioms:\s*\[[\s\S]*?\]|does not depend on any axioms)",out.read_text()) if r['kind']=='lean' else 'N/A'
 r.update(label=label,gnu_wall_seconds=wall,receipt_sha256=sha(p),output_sha256=sha(out),time_sha256=sha(tim),axioms=axioms,source_revision_qualification='Raw revision is the recorded host baseline; exact dirty development inputs are pinned by the per-attempt source snapshot/hash and complete direct dependency artifacts, with transitive h6 audit. Do not attribute a dirty snapshot to a later commit.')
 scopes.append(r)
lean=[r for r in scopes if r['kind']=='lean'];native=[r for r in scopes if r['kind']=='native']
assert sorted(r['attempt'] for r in lean)==list(range(64100,64200))
assert len(native)==8
assert all(r['admission_exit']==0 and r['admission_allowed'] is True for r in scopes)
latest={}
for r in lean:
 if r['exit']==0:latest[r['module']]=r
for r in lean:
 r['formal_credit']='accepted final job cohort' if latest.get(r['module']) is r else 'failed or superseded development source; no independent final credit'
for r in latest.values():
 assert 'sorryAx' not in r['print_axioms']
 for ax in re.findall(r'depends on axioms:\s*\[([^]]*)\]',r['print_axioms']):assert set(x.strip() for x in ax.split(','))<={'propext','Classical.choice','Quot.sound'}
result=dict(lean_attempts=len(lean),native_scopes=len(native),kani=0,ids=[r['attempt'] for r in lean],failed_lean=[r['attempt'] for r in lean if r['exit']],failed_native=[r['label'] for r in native if r['exit']],all_admissions_compliant=True,all_swaps_zero=all(r['swaps']=='0' for r in scopes),peak_rss_kib=max(int(r['peak_rss_kib']) for r in scopes),total_gnu_wall_seconds=sum(r['gnu_wall_seconds'] or 0 for r in scopes),latest_modules={m:r['attempt'] for m,r in latest.items()},scopes=scopes)
(E/'attempts.json').write_text(json.dumps(result,indent=2)+'\n')
pins=[]
for p in sorted(E.glob('PV_DIAG3_*.lean')):
 pins.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size,git_blob=subprocess.check_output(['git','hash-object',str(p)],text=True).strip(),accepted_attempt=latest[p.stem]['attempt'],object_sha256=latest[p.stem]['object_sha256']))
(E/'final-source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['scopes','ids','latest_modules']},indent=2))
