"""Summarize every scoped attempt, including rejected proof results."""
from pathlib import Path
import json,hashlib,csv,re,lzma
E=Path(__file__).resolve().parent;rows=[]
for p in sorted(E.glob('NNP_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());ax=r['print_axioms'];log=(p.parent/'stdout.log').read_text()
 if r['kind']=='audit':ax=re.findall(r"'[^']+' (?:depends on axioms:\s*\[[^\]]*\]|does not depend on any axioms)",log)
 rows.append(dict(attempt=r['attempt'],target=r['module'],exact_command=json.dumps(r['command']),exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swap=r['swaps'],source_revision=r['source_revision'],source_sha256=json.dumps(r['source_hashes']),deps_fingerprint_sha256=hashlib.sha256(json.dumps(r['deps_fingerprint'],sort_keys=True).encode()).hexdigest(),print_axioms=json.dumps(ax),scope=r['cgroup'],limits=json.dumps(r['limits']),receipt=str(p.relative_to(E))))
outer=E/'NNP_L016/receipt.json'
if outer.exists():
 r=json.loads(outer.read_text())
 for p in sorted(E.glob('NNP_FINAL_*.json')):
  sub=json.loads(p.read_text());base=next(x.copy() for x in rows if x['attempt']=='NNP_L016')
  base.update(attempt='NNP_L016/'+sub['target'],target=sub['target'],exact_command=json.dumps(sub['command']),exit_status=sub['exit_status'],wall_seconds=sub['wall_seconds'],peak_rss_kib=sub['peak_rss_kib'],swap=sub['swaps'],print_axioms=json.dumps(sub['print_axioms']),receipt=p.name)
  rows.append(base)
with (E/'NNP_COMPILE.tsv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]),delimiter='\t');w.writeheader();w.writerows(rows)
with (E/'NNP_TRANSCRIPT.tsv').open('w') as f:
 f.write('attempt\ttarget\texit\twall_seconds\tpeak_rss_kib\tswap\n')
 for r in rows:f.write('\t'.join(str(r[k]) for k in ['attempt','target','exit_status','wall_seconds','peak_rss_kib','swap'])+'\n')
# No failed attempt's sorryAx report is accepted as proof evidence.
for p in E.rglob('*'):
 if p.is_file() and p.stat().st_size>20_000_000:
  raw=p.read_bytes();p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw,preset=6));p.with_name(p.name+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n');p.unlink()
print(json.dumps(dict(scopes=len(list(E.glob('NNP_L[0-9][0-9][0-9]/receipt.json'))),results=len(rows),passed=sum(r['exit_status']==0 for r in rows),failed=[r['attempt'] for r in rows if r['exit_status']!=0])))
