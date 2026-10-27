from pathlib import Path
import hashlib,json,re
P=Path(__file__).resolve().parent;R=P.parents[1]
receipts=[]
for f in sorted(P.glob('JGx_TX2_*/receipt.json')):
 r=json.loads(f.read_text());r['receipt_path']=str(f.relative_to(R));receipts.append(r)
rows=[];fail=[]
for src in sorted((R/'lean').glob('JGx_*.lean')):
 h=hashlib.sha256(src.read_bytes()).hexdigest();name=src.name
 matches=[r for r in receipts if r['exit_status']==0 and r.get('source_hashes',{}).get(name)==h]
 # Host source_hashes values are manifest dictionaries in some cohorts.
 if not matches:
  matches=[r for r in receipts if r['exit_status']==0 and any((v.get('sha256') if isinstance(v,dict) else v)==h and Path(k).name==name for k,v in r.get('source_hashes',{}).items())]
 if not matches:fail.append(name+': no passing exact-current-hash receipt');continue
 r=matches[-1];stdout=(R/r['receipt_path']).parent.joinpath('stdout.log').read_text()
 theorems=re.findall(r'^(?:@\[[^\n]*\]\s*)?theorem\s+(\w+)',src.read_text(),re.M)
 for t in theorems:
  lines=[l for l in stdout.splitlines() if ('.'+t+"'") in l and ('depends on axioms:' in l or 'does not depend on any axioms' in l)]
  if not lines:fail.append(name+': missing axiom line '+t)
  for line in lines:
   if 'sorryAx' in line:fail.append(name+': rejected recovery axiom '+t)
   if 'depends on axioms:' in line:
    axioms=re.search(r'\[([^]]*)\]',line).group(1).split(', ')
    if set(axioms)-{'propext','Classical.choice','Quot.sound',''}:fail.append(name+': nonstandard axiom '+line)
 if re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s|set_option\s+(maxHeartbeats|maxRecDepth)',src.read_text(),re.M):fail.append(name+': prohibited source pattern')
 rows.append(dict(module=name,sha256=h,attempt=r['attempt'],receipt=r['receipt_path'],theorems=theorems,axioms=r['print_axioms']))
summary=dict(charged_requests=len(list(P.glob('JGx_TX2_[0-9][0-9][0-9].json'))),lean_processes=len(receipts),passed=sum(r['exit_status']==0 for r in receipts),rejected=sum(r['exit_status']!=0 for r in receipts),wall_seconds=sum(r['wall_seconds'] for r in receipts),peak_rss_kib=max([int(r['peak_rss_kib']) for r in receipts]or[0]),swaps=sum(int(r['swaps']) for r in receipts),sources=len(rows),errors=fail)
(P/'JGx_VALIDATION.json').write_text(json.dumps(rows,indent=2)+'\n');(P/'JGx_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n');(P/'JGx_ATTEMPTS.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in receipts))
print(json.dumps(summary,indent=2))
