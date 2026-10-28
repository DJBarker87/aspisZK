"""Archive exact receipts, refusals and sources for only this D414 round."""
from pathlib import Path
import json,shutil,hashlib,re,datetime
from run import H
O=H/'archive-resume7';R=O/'receipts';R.mkdir(parents=True,exist_ok=True);index=[];native=[];snapshot_errors=[];admission_errors=[];refusals=[]
paths=sorted(H.glob('lean-615[0-9][0-9]*'))+sorted(H.glob('llvm227-resume7-*'))
for p in paths:
 if not p.is_dir():continue
 dest=R/p.name;dest.mkdir(exist_ok=True)
 for f in p.rglob('*'):
  if not f.is_file() or f.suffix in ['.olean','.ilean']:continue
  q=dest/f.relative_to(p);q.parent.mkdir(exist_ok=True,parents=True);shutil.copy2(f,q)
 rp=p/'receipt/receipt.json'
 if not rp.exists():
  if (p/'refusal.json').exists():
   refusal=json.loads((p/'refusal.json').read_text());refusal['label']=p.name
   # A refused admission cannot feed an audit or consume a compiler attempt.
   refusals.append(refusal)
  continue
 x=json.loads(rp.read_text());log=(rp.parent/'stdout.log').read_text()+'\n'+(rp.parent/'stderr.log').read_text()
 for name in ['reservation.json','barrier.json']:
  q=p/name
  if not q.exists() or json.loads(q.read_text()).get('allowed')is not True:admission_errors.append(dict(label=p.name,gate=name))
 full=[m.group(0)for m in re.finditer(r"^'([^'\n]+)' (?:depends on axioms:\s*\[[^\]]*\]|does not depend on any axioms)",log,re.M)]
 x['print_axioms']=full if p.name.startswith('lean-') else ['N/A: native optimized LLVM compilation; no Lean declaration']
 x['admission_review']='Both current outer reservation and inner barrier allowed:true; existing run.py requires exit0 as well as allowed:true, in the same guarded invocation. Cooldown checked before admission.'
 if p.name.startswith('lean-'):
  actual=hashlib.sha256((p/'source.lean').read_bytes()).hexdigest()
  if actual!=x['source_sha256']:snapshot_errors.append(dict(label=p.name,expected=x['source_sha256'],actual=actual))
  row=dict(label=p.name,module=x['module'],attempt=x['attempt'],exit=x['exit_status'],wall_seconds=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps'],source_revision=x['source_revision'],lean_source_revision=x['lean_source_revision'],source_sha256=x['source_sha256'],source_snapshot_sha256=actual,print_axioms=full,receipt='receipts/'+p.name+'/receipt/receipt.json')
  index.append(row)
 else:native.append(dict(label=p.name,exit=x['exit_status'],wall_seconds=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps'],source_revision=x['source_revision'],command=x['command'],print_axioms=x['print_axioms'],receipt='receipts/'+p.name+'/receipt/receipt.json'))
 (dest/'receipt/receipt.json').write_text(json.dumps(x,indent=2)+'\n')
# Verify180-second refusal cooldowns against the next outer admission time.
def utc(p):return datetime.datetime.fromisoformat(json.loads(p.read_text())['utc']).timestamp()
refusal_timing=[]
for r in refusals:
 p=H/r['label'];q=p/'reservation.json'
 if not q.exists():continue
 start=max(utc(q),(p/'refusal.json').stat().st_mtime);after=[]
 for p2 in paths:
  if not (p2/'reservation.json').exists():continue
  t=utc(p2/'reservation.json')
  if t>start:after.append((t,p2.name))
 if after:
  t,label=min(after);delay=t-start
  refusal_timing.append(dict(refused=r['label'],next_admission=label,elapsed_seconds=delay,required=180,compliant=delay>=180))
  if delay<180:admission_errors.append(dict(refused=r['label'],next_admission=label,cooldown_seconds=delay))
for name in ['TALLY-resume7.json','project-resolution-resume7.json','external-verification-resume7.json']:
 shutil.copy2(H/name,O/name)
for name,data in [('receipt-index.json',index),('native-receipt-index.json',native),('source-snapshot-check.json',dict(checked=len(index),mismatches=snapshot_errors)),('admission-audit.json',dict(errors=admission_errors,refusals=refusals,refusal_timing=refusal_timing,void_attempts=[] if not admission_errors else 'REVIEW REQUIRED; do not consume affected artifacts'))]:
 (O/name).write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps(dict(lean_receipts=len(index),native_receipts=len(native),snapshot_errors=snapshot_errors,admission_errors=admission_errors)))
