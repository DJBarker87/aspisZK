from pathlib import Path
import json,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-2tnv-20261028/resume';rows=[json.load(open(p)) for p in sorted(E.glob('receipt-*.json'))]
for r in rows:
 s=R/r['source_path'];assert hashlib.sha256(s.read_bytes()).hexdigest()==r['source_sha256'] or not r['accepted'],(r['attempt'],'accepted source changed')
 if r['accepted']:
  assert not any(a in (E/f"out-{r['attempt']}.log").read_text() for a in ['sorryAx','error:'])
  assert r['swaps']==0 and r['peak_rss_kib']<8*1024*1024
result=dict(charged=len(rows),passed=sum(r['accepted'] for r in rows),failed=[r['attempt'] for r in rows if not r['accepted']],wall_seconds=sum(r['wall_seconds'] for r in rows),peak_rss_kib=max(r['peak_rss_kib'] for r in rows),swaps=sum(r['swaps'] for r in rows),kani=0,agg16=0,attempts=rows)
(E/'VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k!='attempts'})
