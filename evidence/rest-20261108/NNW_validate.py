"""Validate focused receipts and generate the section-6 compile index."""
from pathlib import Path
import hashlib,json,re,csv,lzma
E=Path(__file__).resolve().parent
standard={'propext','Classical.choice','Quot.sound'}
rows=[]
for p in sorted(E.glob('NNW_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];d=p.parent
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['timeout']==180 and r['swaps']=='0'
 ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
 ds=json.loads((E/(a+'-disk-0.json')).read_text());assert ds['free']>=40_000_000_000
 attempts=[json.loads(l) for l in (E/'NNW_ATTEMPTS.jsonl').read_text().splitlines() if json.loads(l)['attempt']==a]
 assert any(x.get('event')=='share_check' and x['host']['count']<6 for x in attempts)
 for name,h in r['source_hashes'].items():assert hashlib.sha256((d/'sources'/name).read_bytes()).hexdigest()==h
 log=(d/'stdout.log').read_text();axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log)
 if r['exit_status']==0:
  assert 'error:' not in log
  if r['kind']=='raw_ax2':
   result=json.loads(next(l.removeprefix('NEP_RESULT ') for l in log.splitlines() if l.startswith('NEP_RESULT ')))
   assert result['root']=='AspisR1.NNW_Rest.assemble' and result['equal'] is True
   assert set(result['walked_axioms'])==set(result['collect_axioms'])==standard
   assert 'NEP_FAILURE' not in log
   for z in d.glob('*.xz'):
    assert hashlib.sha256(lzma.decompress(z.read_bytes())).hexdigest()==z.with_suffix('.sha256').read_text().strip()
   (E/'NNW_RAW_AX2_RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
  for line in axioms:
   if 'depends on axioms:' in line:assert set(line.split('[')[1].rstrip(']').split(', '))<=standard,line
 rows.append([a,r['module'],r['exit_status'],r['wall_seconds'],r['peak_rss_kib'],r['swaps'],r['source_revision'],json.dumps(r['source_hashes']),hashlib.sha256(json.dumps(r['deps_fingerprint'],sort_keys=True).encode()).hexdigest(),' | '.join(axioms),json.dumps(r['command'])])
with (E/'NNW_COMPILE.tsv').open('w') as f:
 w=csv.writer(f,delimiter='\t');w.writerow(['attempt','target','exit','wall_seconds','peak_RSS_KiB','swap','source_revision','source_sha256','deps_fingerprint_sha256','print_axioms','argv']);w.writerows(rows)
print(json.dumps(dict(attempts=len(rows),passed=sum(r[2]==0 for r in rows),failed=sum(r[2]!=0 for r in rows),wall_seconds=sum(r[3] for r in rows),peak_rss_kib=max(int(r[4]) for r in rows))))
