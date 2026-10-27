from pathlib import Path
import json,hashlib,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[];valid={};bad=[]
for n in range(1,101):
 a=f'JGw26_{n:03}';f=P/a/'receipt.json'
 if not f.exists():
  assert n==47,n
  c=json.loads((P/(a+'.json')).read_text())
  c.update(exit_status=None,status='dependency preflight rejection before Lean; launcher exit not independently retained',wall_seconds=None,peak_rss_kib=None,swaps=None,print_axioms=['N/A: no Lean process'],source_hashes={'JGw_DotInner.lean':sha((R/'lean/JGw_DotInner.lean').read_bytes())})
  (P/'JGw_PRELEAN047.json').write_text(json.dumps(c,indent=2)+'\n')
  rows.append(c);continue
 c=json.loads(f.read_text());rows.append(c)
 if c['exit_status']==0:
  for name,h in c['source_hashes'].items():valid[(name,h)]=a
  for line in c['print_axioms']:
   if 'sorryAx' in line:bad.append((a,line))
 else:bad.append((a,c['exit_status']))
(P/'JGw_ATTEMPTS.jsonl').write_text(''.join(json.dumps(c,sort_keys=True)+'\n' for c in rows))
manifest=[];missing_axioms=[]
for f in sorted((R/'lean').glob('JGw_*.lean')):
 h=sha(f.read_bytes());a=valid.get((f.name,h));assert a,(f,'no current-hash passing receipt')
 c=next(c for c in rows if c['attempt']==a)
 text=f.read_text();ns=None
 for line in text.splitlines():
  m=re.match(r'namespace AspisR1\.(JGw_\w+)',line)
  if m:ns=m[1]
  m=re.match(r'theorem (\w+)',line)
  if m:
   root=f'AspisR1.{ns}.{m[1]}'
   if not any("'"+root+"'" in ax for ax in c['print_axioms']):missing_axioms.append((f.name,root,a))
 manifest.append(dict(module=f.stem,source_sha256=h,bytes=f.stat().st_size,passing_attempt=a,print_axioms=c['print_axioms']))
assert not missing_axioms,missing_axioms
(P/'JGw_SOURCES.json').write_text(json.dumps(manifest,indent=2)+'\n')
passed=[r for r in rows if r['exit_status']==0];failed=[r for r in rows if r['exit_status'] not in (0,None)]
summary=dict(charged_requests=100,lean_processes=99,passed=len(passed),failed=len(failed),prelean=1,kani=0,wall_seconds=sum(r['wall_seconds'] or 0 for r in rows),peak_rss_kib=max(int(r['peak_rss_kib'] or 0) for r in rows),successful_peak_rss_kib=max(int(r['peak_rss_kib'] or 0) for r in passed),swaps=sum(int(r['swaps'] or 0) for r in rows),delivered_modules=len(manifest),missing_theorem_audits=missing_axioms,failed_attempts=[r['attempt'] for r in failed],no_standard_axiom_violations_in_passes=not any('sorryAx' in ax for r in passed for ax in r['print_axioms']))
(P/'JGw_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
source=(R/'lean/FJv_Top.lean').read_bytes()
base=subprocess.check_output(['git','show','e93480e196:lean/FJv_Top.lean']);assert source==base
for tag in ['BEFORE','AFTER']:(P/f'JGw_FJv_Top_{tag}.lean.txt').write_bytes(source)
(P/'JGw_LEDGER_DELTA.json').write_text(json.dumps(dict(target='AspisR1.FJv_Top.deployed',method='Quantified atomic-law-family/conjunction-leaf; shared witnesses, deployment rows, guards and carriers retained, design/PREMISE-LEDGER-20261025.md FJv section lines2993ff',before=dict(T=83,P=3,G=13,C=0),after=dict(T=83,P=3,G=13,C=0),deployment_before=dict(T=89,P=19,G=13,C=0),deployment_after=dict(T=89,P=19,G=13,C=0),removed=dict(T=0,P=0,G=0,C=0),added=dict(T=0,P=0,G=0,C=0),changed=dict(T=0,P=0,G=0,C=0),source_sha256=sha(source),byte_identical=True,nonvacuity='Only local source-helper constructions; no accepted1/accepted2 or joint fixture',note='Read-only JGv handoff quotes deployment20P; current authoritative ledger FJv row says19P. We follow ledger row verbatim; no new recount credit.'),indent=2)+'\n')
print(json.dumps(summary,indent=2))
