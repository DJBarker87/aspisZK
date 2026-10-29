from pathlib import Path
import json,hashlib,re,subprocess
D=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[];accepted={}
for p in sorted(D.glob('lean*-receipt.json')):
 r=json.loads(p.read_text());n=r['attempt'];prefix=D/f'lean{n}'
 assert r['admission_exit']==0 and r['admission_allowed'] is True
 assert sha(Path(str(prefix)+'-source.lean.txt'))==r['source_sha256']
 assert r['swaps']=='0'
 out=Path(str(prefix)+'-output.log').read_text()
 ax=re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",out)
 if r['exit']==0:
  assert 'sorryAx' not in out
  for a in re.findall(r'depends on axioms: \[([^]]*)\]',out):assert set(a.split(', '))<={'propext','Classical.choice','Quot.sound'}
  accepted[r['module']]=r
 rows.append(dict(attempt=n,module=r['module'],exit=r['exit'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],source_sha256=r['source_sha256'],print_axioms=ax))
for m in ['PV_SKW_DIAG_FILE','PV_SKW_DIAG_JSON_STDOUT','PV_SKW_DIAG_ERROR_STDERR','PV_SKW_L1']:
 r=accepted[m];assert sha(D/(m+'.lean'))==r['source_sha256']
summary=dict(attempts=len(rows),passes=sum(r['exit']==0 for r in rows),failures=[r['attempt'] for r in rows if r['exit']!=0],wall_seconds=sum(r['wall_seconds'] for r in rows),peak_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swaps=0,native_scopes=0,Kani=0,source_guard_sha256=sha(D/'run.py'),combined_audit='FAILED: no credit',accepted_witness_modules={m:r['attempt'] for m,r in accepted.items() if m.startswith('PV_SKW_')},rows=rows)
(D/'validation-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
# Exercise the exact failed-source guard block without admission or compiler launch.
s=(D/'run.py').read_text();start=s.index(" for old in D.glob('lean*-receipt.json'):");end=s.index(" obj=D/'objects'",start)
block=s[start:end];block='\n'.join(line[1:] for line in block.splitlines())
failed=json.loads((D/'lean68707-receipt.json').read_text())
ns=dict(D=D,json=json,sha=sha,src=D/'lean68707-source.lean.txt')
try:exec(block,ns);raise RuntimeError('guard failed to reject')
except AssertionError as e:
 assert str(e)=='unchanged failed source'
 (D/'guard-test.json').write_text(json.dumps(dict(rejected=True,message=str(e),source_sha256=failed['source_sha256'],guard_sha256=sha(D/'run.py'),compiler_launched=False),indent=2)+'\n')
print({k:v for k,v in summary.items() if k not in {'rows'}})
